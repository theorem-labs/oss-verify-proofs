(* check_copy's instruction segments, fuzz_wire ubsan 6e91fe0b5555 (fuzz_wire.c:184-210, untagged :172-182 and fuzz.h's
   fuzz_dup inlined):
   - cc_segA 0x13550..0x1358c: the frame, the rp_copy_untag call (rp_copy_untag_contract), fuzz_dup's malloc size
     (fds_eq: the seqz / add pair is malloc(n ? n : 1)), up to the `jal malloc`;
   - cc_front 0x13590..0x136a8: fuzz_dup's NULL test and memcpy(u, f, n) (n != 0), untagged's tag test on f (bytes 12,
     13, 16, 17) and its memcpy(u + 12, f + 16, n - 16), the want test on u (cc_uchk), `got != want` (cc_eq), got &&
     bcmp(c, u, got) (bcmp_contract), up to the `jal free`;
   - cc_seg_epi 0x136ac..0x136cc: the epilogue.
   UBSan traps (each a branch to the `unimp` at 0x136d4), refuted: the pointer-overflow checks on f + 12 .. f + 17
   (0x135b8, 0x135d0, 0x135e4, 0x13600, 0x13618: f + n <= 2^64 with n >= 18) and on u + 12 .. u + 17 (0x13620,
   0x13640, 0x13654, 0x13668, 0x13678: u + fuzz_dup_size n < 2^63).
   untagged (fuzz_wire.c:172-182):
     static uint8_t *untagged(const uint8_t *f, size_t n, size_t *len)
     {
       uint8_t *u = fuzz_dup(f, n);
       if (n >= 18 && w_is_tag(f) && w_is_reac(f, 16)) {
         memcpy(u + 12, f + 16, n - 16);
         *len = n - 4;
       } else {
         *len = n;
       }
       return u;
     }
   with fuzz.h's w_is_reac(f, at) = f[at] == 0x88 && f[at + 1] == 0x19, w_is_tag(f) = f[12] == 0x81 && f[13] == 0x00
   and w_is_audio(f) = f[16] == 0x00 && f[17] == 0x00 (fuzz.h:37-50); ut_bytes / ut_len are u's bytes and *len.
   got_want: check_copy's want (n >= 50 && w_is_reac(u, 12) && w_is_audio(u) ? ulen : 0) is copy_untag_result n bs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import FrameBytes rp_copy_untag_c memcpy_c bcmp_c FuzzDup.
Import ListNotations.
Open Scope Z_scope.

Definition CC_MALLOC : Z := 0x14898.

Definition cc_sA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (c f n : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1,
    ms' = MS (mkR (Z_to_bv 64 0x13590) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
               (Z_to_bv 64 (copy_untag_result n bs)) (Z_to_bv 64 c) (Z_to_bv 64 (fuzz_dup_size n)) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 n) (Z_to_bv 64 f) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CC_MALLOC) fc None m1 (seg_rom rsegs) /\
    munch ((bv_unsigned sp - 80, bv_unsigned sp) :: cu_footprint c n bs) m m1 /\ wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    bytes_at rsegs m1 c (cu_bytes n bs).

Lemma fds_eq : forall n, 0 <= n < 2^63 ->
  Z_to_bv 64 (n + bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)) = Z_to_bv 64 (fuzz_dup_size n).
Proof.
  intros n Hn. unfold fuzz_dup_size. destruct (Z.eqb_spec n 0) as [->|E]; [vm_compute; reflexivity|].
  unfold v_sltiu, c_ltu, bv_ltu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  rewrite (proj2 (Z.ltb_ge n 1)) by lia. rewrite (unsigned_lit 0) by lia. f_equal. lia.
Qed.

Lemma cc_segA : rp_copy_untag_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c f n : Z) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp -> mem_inv rsegs m ->
    0 <= n <= 1600 -> Z.of_nat (length bs) = n -> u8arr rsegs m c bs -> 8 <= c ->
    c + n <= bv_unsigned sp - 80 -> 0 <= f < 2^64 ->
    evt rsegs (cc_sA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c f n bs m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 f) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13550) fc None m (seg_rom rsegs)).
Proof.
  intros HCU ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c f n bs lo
    ST LO MI HN HL CB HC8 DJ HF.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 12 step.
  eapply evt_cut.
  { eapply HCU with (lo := lo) (bs := bs); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia.
    - exact ST.
    - lia.
    - exact MI.
    - rewrite !unsigned_lit by lia. intros _. split; [exact CB|]. split; [lia|]. split; [lia|]. split; [lia|]. lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & WM2 & MI2 &
    ST2 & MU2 & CB2).
  rewrite !(unsigned_lit (bv_unsigned sp + -48)) in * by lia. rewrite !(unsigned_lit c), !(unsigned_lit n) in * by lia.
  replace (ret_pc (Z_to_bv 64 79232)) with (Z_to_bv 64 79232) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 4 step.
  rewrite fds_eq by lia.
  pose proof (bytes_at_bound _ _ _ _ (proj1 CB)) as CBB.
  assert (FP : cu_footprint c n bs = [] \/ (50 <= n /\ cu_footprint c n bs = [(c + 12, c + n - 4)])).
  { unfold cu_footprint, cu_moves. destruct (Z.leb_spec 50 n); cbn [andb]; [|left; reflexivity].
    destruct (cu_tagged bs); [right; split; [lia | reflexivity] | left; reflexivity]. }
  apply evt_done. unfold cc_sA_post.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2. split; [reflexivity|].
  split.
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in Hx |- *. destruct Hx as [Hx _]. split; [lia | exact I].
    - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx |- *. destruct Hx as [Hx Hy].
      split; [lia | exact Hy]. }
  split; [exact (wmono_trans _ _ _ _ WM WM2)|]. split; [exact MI2|].
  split.
  { eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 |].
    destruct FP as [FP | (_ & FP)]; rewrite FP; cbn [disjoint_from cells_size csize Nat.add]; lia. }
  destruct (Z.ltb_spec n 50) as [LT|GE].
  - assert (E : cu_bytes n bs = bs) by (unfold cu_bytes, cu_moves; rewrite (proj2 (Z.leb_gt 50 n) LT); reflexivity).
    rewrite E. eapply bytes_at_transport; [exact (proj1 CB) | exact MU2 |].
    destruct FP as [FP | (H50 & _)]; [|lia]. rewrite FP. cbn [disjoint_from]. rewrite HL. lia.
  - exact (proj1 (CB2 GE)).
Qed.


Definition CC_FREE : Z := 0x14758.

Ltac take_false tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => replace cnd with false; [cbv iota | symmetry; tac] end.
Ltac take_true tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => replace cnd with true; [cbv iota | symmetry; tac] end.

Lemma bveqb_u : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* decide a branch condition on words whose values lia knows *)
Ltac bvc := unfold bv_ltu, bv_eqb, zxb; fold_lit_ux; repeat (match goal with
    | |- context [bv_unsigned (Z_to_bv 64 (Z.neg ?p))] =>
        let v := eval vm_compute in (Z.neg p mod 2 ^ 64) in
        replace (bv_unsigned (Z_to_bv 64 (Z.neg p))) with v by (rewrite unsigned_lit_wrap; vm_compute; reflexivity)
    | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
    end);
  first [ rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia
        | rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia ]; reflexivity.

Lemma rdz : forall m a bs k, bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof. intros m a bs k H Hk. pose proof (rd1 m a bs (Z.to_nat k) H ltac:(lia)) as R. rewrite Z2Nat.id in R by lia. exact R. Qed.

Ltac zdec := repeat match goal with |- context [?x =? ?y] =>
  first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia] end; cbn [andb].

Lemma fds_cases : forall n, 0 <= n -> 1 <= fuzz_dup_size n /\ (0 < n -> fuzz_dup_size n = n) /\ (n = 0 -> fuzz_dup_size n = 1).
Proof. intros n H. unfold fuzz_dup_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma cu_bytes_length : forall n bs, 16 <= n -> Z.of_nat (length bs) = n -> length (cu_bytes n bs) = length bs.
Proof.
  intros n bs H1 H2. unfold cu_bytes. destruct (cu_moves n bs); [|reflexivity].
  apply upd_bytes_length. rewrite firstn_length, skipn_length. lia.
Qed.

(* untagged's frame (fuzz_wire.c:172-182) as the u buffer holds it after fuzz_dup's and untagged's memcpy calls *)
Definition ut_bytes (n : Z) (bs : list byte) : list byte :=
  if (18 <=? n) && cu_tagged bs then upd_bytes bs 12 (firstn (Z.to_nat (n - 16)) (skipn 16 bs)) else bs.
Definition ut_len (n : Z) (bs : list byte) : Z := if (18 <=? n) && cu_tagged bs then n - 4 else n.

Lemma memcmp_same : forall l k, (k <= length l)%nat -> memcmp_model l l k = Some 0.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l H; [reflexivity|].
  destruct l as [|b l]; cbn in H; [lia|]. cbn. rewrite Z.eqb_refl. apply IH. lia.
Qed.

Definition cc_sB_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 sv0 sv1 sv3 sv4 : word) (F : bvmap 5 word) (fc : bv 32)
    (u n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x136ac) sp gp tp t0 t1 t2 sv0 sv1 (Z_to_bv 64 u) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 u) sv3 sv4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CC_FREE) fc None m' (seg_rom rsegs) /\
    munch [(u, u + fuzz_dup_size n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma got_want : forall n bs, 0 <= n -> copy_untag_result n bs =
  if n <? 50 then 0 else
  if (bv_unsigned (nth 12 (ut_bytes n bs) (Z_to_bv 8 0)) =? 0x88) && (bv_unsigned (nth 13 (ut_bytes n bs) (Z_to_bv 8 0)) =? 0x19)
     && (bv_unsigned (nth 16 (ut_bytes n bs) (Z_to_bv 8 0)) =? 0) && (bv_unsigned (nth 17 (ut_bytes n bs) (Z_to_bv 8 0)) =? 0)
  then ut_len n bs else 0.
Proof.
  intros n bs Hn. unfold copy_untag_result, ut_bytes, ut_len, cu_bytes, cu_len, cu_moves, cu_byte.
  destruct (Z.ltb_spec n 50); [reflexivity|].
  rewrite (proj2 (Z.leb_le 18 n)), (proj2 (Z.leb_le 50 n)) by lia. reflexivity.
Qed.

Lemma got_le : forall n bs, 0 <= n -> 0 <= copy_untag_result n bs <= n.
Proof.
  intros n bs Hn. unfold copy_untag_result, cu_len, cu_moves.
  destruct (Z.ltb_spec n 50); [lia|].
  destruct (_ && _ && _ && _); [|lia]. destruct (_ && _); lia.
Qed.

Lemma ut_cu : forall n bs, 50 <= n -> ut_bytes n bs = cu_bytes n bs.
Proof.
  intros n bs Hn. unfold ut_bytes, cu_bytes, cu_moves.
  rewrite (proj2 (Z.leb_le 18 n)), (proj2 (Z.leb_le 50 n)) by lia. reflexivity.
Qed.

Lemma ut_len_ok : forall n bs, 50 <= n -> 0 < ut_len n bs <= n.
Proof. intros n bs H. unfold ut_len. destruct (_ && _); lia. Qed.

Lemma ut_bytes_length : forall n bs, Z.of_nat (length bs) = n -> length (ut_bytes n bs) = length bs.
Proof.
  intros n bs H. unfold ut_bytes. destruct (Z.leb_spec 18 n); cbn [andb]; [|reflexivity].
  destruct (cu_tagged bs); [|reflexivity]. apply upd_bytes_length. rewrite firstn_length, skipn_length. lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (H1 & H2 & H3)].
    rewrite (cells_bytes_length cs1 W1) in B2.
    split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]).
    + intros i Hi. apply H3. lia.
    + intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply H3. lia.
  - intros [[[W1 B1] (H1 & H2 & H3)] [[W2 B2] (K1 & K2 & K3)]].
    rewrite <- (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption | split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))) as [L|L]; [apply H3; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply K3. lia.
Qed.

Lemma rw1_bytes : forall m A k bs, rw_cells rsegs m A [CB k bs] -> bytes_at rsegs m A bs.
Proof. intros m A k bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma bytes_at_mid : forall m a bs i k, bytes_at rsegs m a bs -> (i + k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
  intros m a bs i k H Hik.
  rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H as [_ H].
  rewrite firstn_length, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma cu_bytes_len : forall n bs, Z.of_nat (length bs) = n -> length (cu_bytes n bs) = length bs.
Proof.
  intros n bs H. unfold cu_bytes. destruct (cu_moves n bs) eqn:E; [|reflexivity].
  unfold cu_moves in E. apply andb_prop in E as [E _]. apply Z.leb_le in E.
  apply upd_bytes_length. rewrite firstn_length, skipn_length. lia.
Qed.

Lemma ut_split : forall n bs, 18 <= n -> Z.of_nat (length bs) = n ->
  firstn 12 bs ++ firstn (Z.to_nat (n - 16)) (skipn 16 bs) ++
    firstn 4 (skipn (Z.to_nat (n - 16)) (skipn 12 bs)) =
  upd_bytes bs 12 (firstn (Z.to_nat (n - 16)) (skipn 16 bs)).
Proof.
  intros n bs H1 H2. unfold upd_bytes. f_equal. f_equal.
  rewrite firstn_length, skipn_length. rewrite skipn_skipn.
  replace (Z.to_nat (n - 16) + 12)%nat with (12 + Init.Nat.min (Z.to_nat (n - 16)) (length bs - 16))%nat by lia.
  apply firstn_all2. rewrite skipn_length. lia.
Qed.

Section SB.
Variables (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (c f n u : Z) (bs : list byte).
Hypothesis HMC : memcpy_contract.
Hypothesis HBC : bcmp_contract.
Hypothesis HN : 0 <= n <= 1600.
Hypothesis HL : Z.of_nat (length bs) = n.
Hypothesis HU1 : 4096 <= u.
Hypothesis HU2 : u + fuzz_dup_size n < 2^63.
Hypothesis DC : u + fuzz_dup_size n <= c \/ c + n <= u.
Hypothesis DF : u + fuzz_dup_size n <= f \/ f + n <= u.
Hypothesis HC : 0 <= c /\ c + n <= 2^64.

Local Notation G := (copy_untag_result n bs).
Local Notation Q := (cc_sB_post sp gp tp s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 G) (Z_to_bv 64 c) (Z_to_bv 64 n)
                      (Z_to_bv 64 f) F fc u n m).
Local Notation BST pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk :=
  (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 G) (Z_to_bv 64 c) x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 u) (Z_to_bv 64 n) (Z_to_bv 64 f) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mk (seg_rom rsegs)).

Lemma cc_free : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) mk,
  munch [(u, u + fuzz_dup_size n)] m mk -> wmono rsegs m mk -> mem_inv rsegs mk ->
  evt rsegs Q (BST 0x136a4 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk).
Proof.
  intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk MU WM MI.
  do 2 step. apply evt_done. unfold cc_sB_post.
  exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, mk.
  split; [reflexivity|]. tauto.
Qed.

Lemma cc_z : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) mk,
  G = 0 -> munch [(u, u + fuzz_dup_size n)] m mk -> wmono rsegs m mk -> mem_inv rsegs mk ->
  evt rsegs Q (BST 0x13684 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk).
Proof.
  intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk G0 MU WM MI.
  step. step. take_false ltac:(rewrite G0; reflexivity).
  step. take_true ltac:(rewrite G0; reflexivity).
  apply cc_free; assumption.
Qed.

Lemma cc_eq : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) mk,
  bytes_at rsegs mk c (cu_bytes n bs) -> bytes_at rsegs mk u (ut_bytes n bs) ->
  munch [(u, u + fuzz_dup_size n)] m mk -> wmono rsegs m mk -> mem_inv rsegs mk ->
  evt rsegs Q (BST 0x13688 x1 x5 x6 x7 (Z_to_bv 64 G) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk BC BU MU WM MI.
  pose proof (got_le n bs ltac:(lia)) as GL. pose proof (fds_cases n ltac:(lia)) as DS.
  step. take_false ltac:(unfold bv_eqb; rewrite Z.eqb_refl; reflexivity).
  step. destruct (Z.eqb_spec G 0) as [G0|G0].
  - take_true ltac:(rewrite G0; reflexivity). apply cc_free; assumption.
  - take_false ltac:(bvc).
    assert (N50 : 50 <= n) by (unfold copy_untag_result in G0; destruct (Z.ltb_spec n 50); [contradiction|lia]).
    rewrite (ut_cu n bs N50) in BU.
    do 4 step.
    eapply evt_cut.
    { eapply HBC with (ls := cu_bytes n bs) (rs := cu_bytes n bs) (v := 0) (m := mk).
      - rewrite unsigned_lit by lia. exact BC.
      - rewrite unsigned_lit by lia. exact BU.
      - apply memcmp_same. rewrite unsigned_lit by lia. rewrite cu_bytes_length by lia. lia.
      - exact MI. }
    intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mk' & -> & MU2 & WM2 & MI2 & _ & _).
    rewrite ret_pc_even by first [lia | reflexivity].
    step. take_false ltac:(bvc).
    apply cc_free.
    + eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. intros x Hx. exact I.
    + exact (wmono_trans _ _ _ _ WM WM2).
    + exact MI2.
Qed.
Lemma cc_uchk : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) mk,
  bytes_at rsegs mk c (cu_bytes n bs) -> bytes_at rsegs mk u (ut_bytes n bs) ->
  munch [(u, u + fuzz_dup_size n)] m mk -> wmono rsegs m mk -> mem_inv rsegs mk ->
  evt rsegs Q (BST 0x13634 x1 x5 x6 x7 (Z_to_bv 64 (ut_len n bs)) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk BC BU MU WM MI.
  pose proof (fds_cases n ltac:(lia)) as DS.
  assert (LU : Z.of_nat (length (ut_bytes n bs)) = n) by (rewrite ut_bytes_length; lia).
  pose proof (got_want n bs ltac:(lia)) as GW.
  step. step. destruct (Z.ltb_spec n 50) as [N50|N50].
  { take_true ltac:(bvc). apply cc_z; try assumption; rewrite GW; reflexivity. }
  take_false ltac:(bvc). cbv iota in GW.
  do 2 step. take_false ltac:(bvc).
  pose proof (rdz mk u _ 12 BU ltac:(lia)) as R. step. clear R. change (Z.to_nat 12) with 12%nat.
  set (b12 := bv_unsigned (nth 12 (ut_bytes n bs) (Z_to_bv 8 0))) in GW.
  pose proof (byte_range (nth 12 (ut_bytes n bs) (Z_to_bv 8 0))) as RB12.
  step. step. destruct (Z.eqb_spec b12 136) as [E12|E12].
  2:{ take_true ltac:(subst b12; bvc). apply cc_z; try assumption; rewrite GW; zdec; reflexivity. }
  take_false ltac:(subst b12; bvc).
  do 2 step. take_false ltac:(bvc).
  pose proof (rdz mk u _ 13 BU ltac:(lia)) as R. step. clear R. change (Z.to_nat 13) with 13%nat.
  set (b13 := bv_unsigned (nth 13 (ut_bytes n bs) (Z_to_bv 8 0))) in GW.
  pose proof (byte_range (nth 13 (ut_bytes n bs) (Z_to_bv 8 0))) as RB13.
  step. step. destruct (Z.eqb_spec b13 25) as [E13|E13].
  2:{ take_true ltac:(subst b13; bvc). apply cc_z; try assumption; rewrite GW; zdec; reflexivity. }
  take_false ltac:(subst b13; bvc).
  do 2 step. take_false ltac:(bvc).
  pose proof (rdz mk u _ 16 BU ltac:(lia)) as R. step. clear R. change (Z.to_nat 16) with 16%nat.
  set (b16 := bv_unsigned (nth 16 (ut_bytes n bs) (Z_to_bv 8 0))) in GW.
  pose proof (byte_range (nth 16 (ut_bytes n bs) (Z_to_bv 8 0))) as RB16.
  step. destruct (Z.eqb_spec b16 0) as [E16|E16].
  2:{ take_true ltac:(subst b16; bvc). apply cc_z; try assumption; rewrite GW; zdec; reflexivity. }
  take_false ltac:(subst b16; bvc).
  do 2 step. take_false ltac:(bvc).
  pose proof (rdz mk u _ 17 BU ltac:(lia)) as R. step. clear R. change (Z.to_nat 17) with 17%nat.
  set (b17 := bv_unsigned (nth 17 (ut_bytes n bs) (Z_to_bv 8 0))) in GW.
  pose proof (byte_range (nth 17 (ut_bytes n bs) (Z_to_bv 8 0))) as RB17.
  step. destruct (Z.eqb_spec b17 0) as [E17|E17].
  2:{ take_false ltac:(subst b17; bvc). apply cc_z; try assumption; rewrite GW; zdec; reflexivity. }
  take_true ltac:(subst b17; bvc).
  assert (EG : ut_len n bs = G).
  { rewrite GW. zdec. reflexivity. }
  rewrite EG. apply cc_eq; assumption.
Qed.



Lemma cc_uchk2 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) mk,
  x10 = Z_to_bv 64 (ut_len n bs) ->
  bytes_at rsegs mk c (cu_bytes n bs) -> bytes_at rsegs mk u (ut_bytes n bs) ->
  munch [(u, u + fuzz_dup_size n)] m mk -> wmono rsegs m mk -> mem_inv rsegs mk ->
  evt rsegs Q (BST 0x13634 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk).
Proof. intros. subst x10. apply cc_uchk; assumption. Qed.

Lemma cc_notag : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) mk,
  cu_tagged bs = false -> bytes_at rsegs mk c (cu_bytes n bs) -> bytes_at rsegs mk u bs ->
  munch [(u, u + fuzz_dup_size n)] m mk -> wmono rsegs m mk -> mem_inv rsegs mk ->
  evt rsegs Q (BST 0x13634 x1 x5 x6 x7 (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mk T BC BU MU WM MI.
  assert (E1 : ut_len n bs = n) by (unfold ut_len; rewrite T, andb_false_r; reflexivity).
  assert (E2 : ut_bytes n bs = bs) by (unfold ut_bytes; rewrite T, andb_false_r; reflexivity).
  apply cc_uchk2; [rewrite E1; reflexivity | exact BC | rewrite E2; exact BU | exact MU | exact WM | exact MI].
Qed.

Lemma cc_front : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word) junk,
  bytes_at rsegs m c (cu_bytes n bs) -> bytes_at rsegs m f bs ->
  rw_cells rsegs m u [CB (Z.to_nat (fuzz_dup_size n)) junk] -> mem_inv rsegs m ->
  evt rsegs Q (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 G) (Z_to_bv 64 c) (Z_to_bv 64 u) x11 x12 x13 x14 x15 x16 x17
                   x18 (Z_to_bv 64 n) (Z_to_bv 64 f) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x13590) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 junk BC BF WU MI.
  pose proof (fds_cases n ltac:(lia)) as (DS1 & DS2 & DS3).
  pose proof (bytes_at_bound _ _ _ _ BF) as BFB. rewrite HL in BFB.
  assert (LC : Z.of_nat (length (cu_bytes n bs)) = n) by (rewrite cu_bytes_len; lia).
  pose proof (munch_refl [(u, u + fuzz_dup_size n)] m) as MU0. pose proof (wmono_refl rsegs m) as WM0.
  step. take_false ltac:(bvc). step. step.
  destruct (Z.eqb_spec n 0) as [N0|N0];
    [take_true ltac:(bvc); apply cc_z; try assumption; unfold copy_untag_result;
     rewrite (proj2 (Z.ltb_lt n 50)) by lia; reflexivity|].
  take_false ltac:(bvc).
  pose proof DC as DC'. pose proof DF as DF'. rewrite (DS2 ltac:(lia)) in WU, MU0, DF', DC'.
  do 4 step.
  eapply evt_cut.
  { eapply HMC with (m := m) (src := bs) (junk := junk);
      rewrite ?(unsigned_lit u), ?(unsigned_lit f), ?(unsigned_lit n) by lia.
    - exact BF.
    - lia.
    - exact WU.
    - lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 &
    MI1 & WU1 & BF1).
  rewrite !(unsigned_lit u), !(unsigned_lit f), !(unsigned_lit n) in * by lia.
  rewrite ret_pc_even by first [lia | reflexivity].
  pose proof (bytes_at_transport rsegs _ _ _ _ _ BC MU1 ltac:(cbn [disjoint_from]; rewrite LC; lia)) as BC1.
  step. step. destruct (Z.ltb_spec n 18) as [N18|N18];
    [take_true ltac:(bvc); apply cc_z;
     [unfold copy_untag_result; rewrite (proj2 (Z.ltb_lt n 50)) by lia; reflexivity
     | rewrite (DS2 ltac:(lia)); exact MU1 | exact WM1 | exact MI1]|].
  take_false ltac:(bvc).
  assert (MUa : munch [(u, u + fuzz_dup_size n)] m m1) by (rewrite (DS2 ltac:(lia)); exact MU1).
  pose proof (rw1_bytes _ _ _ _ WU1) as BU1.
  assert (TT : cu_tagged bs = (bv_unsigned (nth 12 bs (Z_to_bv 8 0)) =? 0x81) && (bv_unsigned (nth 13 bs (Z_to_bv 8 0)) =? 0)
      && (bv_unsigned (nth 16 bs (Z_to_bv 8 0)) =? 0x88) && (bv_unsigned (nth 17 bs (Z_to_bv 8 0)) =? 0x19))
    by reflexivity.
  pose proof (byte_range (nth 12 bs (Z_to_bv 8 0))) as RB12. pose proof (byte_range (nth 13 bs (Z_to_bv 8 0))) as RB13.
  pose proof (byte_range (nth 16 bs (Z_to_bv 8 0))) as RB16. pose proof (byte_range (nth 17 bs (Z_to_bv 8 0))) as RB17.
  do 2 step. take_false ltac:(bvc).
  pose proof (rdz m1 f bs 12 BF1 ltac:(lia)) as R. step. clear R. change (Z.to_nat 12) with 12%nat.
  step. step. step.
  destruct (Z.eqb_spec (bv_unsigned (nth 12 bs (Z_to_bv 8 0))) 0x81) as [T12|T12];
    [| take_true ltac:(bvc); apply cc_notag; try assumption; rewrite TT; zdec; reflexivity].
  take_false ltac:(bvc).
  do 2 step. take_false ltac:(bvc).
  pose proof (rdz m1 f bs 13 BF1 ltac:(lia)) as R. step. clear R. change (Z.to_nat 13) with 13%nat.
  step. step.
  destruct (Z.eqb_spec (bv_unsigned (nth 13 bs (Z_to_bv 8 0))) 0) as [T13|T13];
    [| take_true ltac:(bvc); apply cc_notag; try assumption;
       rewrite TT; zdec; reflexivity].
  take_false ltac:(bvc).
  do 2 step. take_false ltac:(bvc).
  pose proof (rdz m1 f bs 16 BF1 ltac:(lia)) as R. do 2 step. clear R. change (Z.to_nat 16) with 16%nat.
  step. step. step.
  destruct (Z.eqb_spec (bv_unsigned (nth 16 bs (Z_to_bv 8 0))) 0x88) as [T16|T16];
    [| take_true ltac:(bvc); apply cc_notag; try assumption;
       rewrite TT; zdec; reflexivity].
  take_false ltac:(bvc).
  do 2 step. take_false ltac:(bvc).
  pose proof (rdz m1 f bs 17 BF1 ltac:(lia)) as R. step. clear R. change (Z.to_nat 17) with 17%nat.
  step. step. step.
  destruct (Z.eqb_spec (bv_unsigned (nth 17 bs (Z_to_bv 8 0))) 0x19) as [T17|T17];
    [| take_true ltac:(bvc); apply cc_notag; try assumption;
       rewrite TT; zdec; reflexivity].
  take_false ltac:(bvc).
  assert (TG : cu_tagged bs = true) by (rewrite TT; zdec; reflexivity).
  do 2 step. take_false ltac:(bvc).
  do 2 step. take_false ltac:(bvc).
  do 3 step.
  apply (rw_cells_split_CB rsegs _ _ [] _ _ [] [12%nat; Z.to_nat (n - 16); 4%nat]) in WU1; [|cbn [sum_nat]; lia].
  cbn [app mk_CB_cells] in WU1.
  apply (rw_cells_app _ _ [_]) in WU1. destruct WU1 as [WP1 WU1]. cbn [cells_size csize Nat.add Z.of_nat] in WU1.
  apply (rw_cells_app _ _ [_]) in WU1. destruct WU1 as [WS WP3]. cbn [cells_size csize Nat.add] in WP3.
  rewrite ?Nat.add_0_r, Z2Nat.id in WP3 by lia.
  assert (BS : bytes_at rsegs m1 (f + 16) (firstn (Z.to_nat (n - 16)) (skipn 16 bs))).
  { pose proof (bytes_at_mid m1 f bs 16 (Z.to_nat (n - 16)) BF1 ltac:(lia)) as X. exact X. }
  eapply evt_cut.
  { eapply HMC with (m := m1) (src := firstn (Z.to_nat (n - 16)) (skipn 16 bs))
      (junk := firstn (Z.to_nat (n - 16)) (skipn 12 bs));
      rewrite ?(unsigned_lit (u + 12)), ?(unsigned_lit (f + 16)), ?(unsigned_lit (n + -16)) by lia.
    - exact BS.
    - rewrite firstn_length, skipn_length. lia.
    - replace (Z.to_nat (n + -16)) with (Z.to_nat (n - 16)) by lia. exact WS.
    - lia.
    - exact MI1. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & WS2 & _).
  rewrite ?(unsigned_lit (u + 12)), ?(unsigned_lit (f + 16)), ?(unsigned_lit (n + -16)) in * by lia.
  rewrite ret_pc_even by first [lia | reflexivity].
  pose proof (rw_cells_transport rsegs _ _ _ _ _ WP1 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as WP1'.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ WP3 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as WP3'.
  pose proof (bytes_at_transport rsegs _ _ _ _ _ BC1 MU2 ltac:(cbn [disjoint_from]; rewrite LC; lia)) as BC2.
  replace (Z.to_nat (n + -16)) with (Z.to_nat (n - 16)) in WS2 by lia.
  assert (WU2 : rw_cells rsegs m2 u [CB 12 (firstn 12 bs); CB (Z.to_nat (n - 16)) (firstn (Z.to_nat (n - 16)) (skipn 16 bs));
                  CB 4 (firstn 4 (skipn (Z.to_nat (n - 16)) (skipn 12 bs)))]).
  { apply (rw_cells_app _ _ [_]). split; [exact WP1'|]. cbn [cells_size csize Nat.add Z.of_nat].
    apply (rw_cells_app _ _ [_]). split; [exact WS2|]. cbn [cells_size csize Nat.add]. rewrite ?Nat.add_0_r, Z2Nat.id by lia.
    exact WP3'. }
  destruct WU2 as [[_ BU2] _]. cbn [cells_bytes cbytes] in BU2. rewrite !app_nil_r in BU2.
  rewrite (ut_split n bs N18 HL) in BU2.
  step.
  apply cc_uchk2.
  - unfold ut_len. rewrite TG, (proj2 (Z.leb_le 18 n) N18). cbn [andb]. f_equal; lia.
  - exact BC2.
  - unfold ut_bytes. rewrite TG, (proj2 (Z.leb_le 18 n) N18). exact BU2.
  - eapply munch_trans; [exact MUa|]. eapply munch_weaken; [|exact MU2].
    intros x Hx. cbn [outside] in Hx |- *. rewrite (DS2 ltac:(lia)) in Hx. lia.
  - exact (wmono_trans _ _ _ _ WM1 WM2).
  - exact MI2.
Qed.
End SB.


Lemma cc_seg_epi : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 v1 v2 v3 v4 vra : word),
  rw_cells rsegs m (bv_unsigned sp) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 v0 v1 s0 a1 a2 a3 a4 a5 a6 a7
                                     v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (ret_pc vra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x136ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v1 v2 v3 v4 vra FR.
  pose proof (u64_range sp) as Rsp.
  do 9 step.
  apply evt_done. reflexivity.
Qed.
