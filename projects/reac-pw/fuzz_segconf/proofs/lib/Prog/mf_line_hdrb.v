(** m_file (plain build, image 3776ca44d75c, 0x13fb4): the sub-piece S_MF_HDRB of S_MF_LINE (Prog/mf_cuts.v):
    from the cut HFIND 0x14488 (m_header after its name checks) to the tail 0x143d4.

    Code (the plain build's disassembly):
      0x14488 a0 = c, a1 = nm, a2 = |nm|; `jal m_find` 0x14494; `beqz a0` 0x14498 -> 0x14624
      found:  0x1449c `sd a0, 0x20(sp)` (cur := &seg[i]); `lw` g->gen, `ld` 0x10(sp), `lw` c->gen; `bne` 0x144ac ->
              0x14714; equal: m_refuse(c, line) 0x144b8, `j 0x14714`
      new:    0x14624 `ld a2, 0x10(sp)`, `lw a0, 0(a2)` (n), `blt a0, s11` (32) -> 0x146e0; 0x146e0 n++ (`sw`
              0x146e8), s4 = c + 256 n, memset(s4, 0, 256) 0x146fc, `sd s4, 0x20(sp)`, memcpy(s4, nm, |nm|)
              0x14710, then 0x14714
      full:   0x14630 overflow++ (`sw` 0x14638), m_refuse(c, line) 0x14644, `sd zero, 0x20(sp)`, `j 0x143d4`
      0x14714 `ld`, `lw` c->gen, `ld a1, 0x20(sp)`, `sw a0, 0xfc(a1)` (g->gen = c->gen), `j 0x143d4`.
    Each path ends at the tail with the state SegModel computes (mfu_facts.mh_find): (m_upd c1 i (ms_with_gen gen),
    Some i), (m_set_segs mc (seg ++ [ms_with_gen gen (mseg0 nm)]), Some n) or (m_refuse (overflow + 1) line false,
    None). After every store or call the post is moved to the new memory (mf_common.mf_post_back) with that write
    inside M_FILE_W of the final model, and the loop facts are carried over (mf_ctx_transport, mf_text_transport).
    In the new path the block is not an mconf encoding between n++ and the gen store: its 9236 bytes are tracked
    as one list and rebuilt at the end (mfp_mconf.mconf_enc_append, mseg_enc_new). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c mf_cuts
  mfu_facts mf_common mfp_mconf mfp_facts m_find_c memset_c memcpy_c m_refuse_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Words *)
Lemma hb_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma hb_sx32_u : forall x, 0 <= x < 2 ^ 32 ->
  bv_unsigned (sx32 (Z_to_bv 64 x)) = if x <? 2 ^ 31 then x else x + 2 ^ 64 - 2 ^ 32.
Proof.
  intros x Hx. unfold sx32. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  destruct (Z.ltb_spec x (2 ^ 31)); Z.div_mod_to_equations; lia.
Qed.

Lemma hb_sx32_eqb : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  bv_eqb (sx32 (Z_to_bv 64 x)) (sx32 (Z_to_bv 64 y)) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb.
  destruct (Z.eqb_spec x y) as [->|Hne]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply Hne.
  rewrite (hb_sx32_u x Hx), (hb_sx32_u y Hy) in E.
  destruct (Z.ltb_spec x (2 ^ 31)), (Z.ltb_spec y (2 ^ 31)); lia.
Qed.

Lemma hb_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite (unsigned_lit x), (unsigned_lit y) by lia. reflexivity. Qed.

Lemma hb_lts_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt x (2 ^ 63))) by lia. rewrite (proj2 (Z.ltb_lt y (2 ^ 63))) by lia. reflexivity.
Qed.

Lemma hb_le4_eqm : forall x y : word, bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32 -> le4 x = le4 y.
Proof.
  intros x y H. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned x) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned y) 32) by lia. rewrite H. reflexivity.
Qed.

Lemma hb_le4_sx32 : forall x, 0 <= x < 2 ^ 32 -> le4 (sx32 (Z_to_bv 64 x)) = le4 (Z_to_bv 64 x).
Proof.
  intros x Hx. apply hb_le4_eqm. rewrite (hb_sx32_u x Hx), (unsigned_lit x) by lia.
  destruct (Z.ltb_spec x (2 ^ 31)); [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

Lemma hb_le4_inc : forall r, 0 <= r < 2 ^ 32 ->
  le4 (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 r)) + 1)) = le4 (Z_to_bv 64 (r + 1)).
Proof.
  intros r Hr. apply hb_le4_eqm. unfold sx32. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

(** s4 = c + (n << 8) (0x146e4 / 0x146ec). *)
Lemma hb_shl8 : forall c x, 0 <= x < 2 ^ 64 ->
  Z_to_bv 64 (c + Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 8) = Z_to_bv 64 (c + 256 * x).
Proof.
  intros c x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
Qed.

(** ** Lists *)
Lemma hb_zs_zb : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  unfold zs, zb. induction l as [|x l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hx Hl]; subst.
  cbn [map]. f_equal; [|exact (IH Hl)].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. exact Hx.
Qed.

Lemma hb_length_zb : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma hb_nth_error_ext : forall {A} (l1 l2 : list A), length l1 = length l2 ->
  (forall i, (i < length l1)%nat -> nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A. induction l1 as [|x l1 IH]; intros [|y l2] HL H; cbn [length] in HL; try discriminate; [reflexivity|].
  f_equal.
  - specialize (H 0%nat ltac:(cbn [length]; lia)). cbn [nth_error] in H. injection H as H. exact H.
  - apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(cbn [length]; lia)).
Qed.

Ltac hb_cases :=
  repeat match goal with
         | |- context [Nat.leb ?a ?b] => destruct (Nat.leb_spec a b)
         | |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b)
         end; cbn [andb].

Lemma hb_upd_nest : forall (cs X Y : list byte) k j, (k + length X <= length cs)%nat -> (j + length Y <= length X)%nat ->
  upd_bytes (upd_bytes cs k X) (k + j) Y = upd_bytes cs k (upd_bytes X j Y).
Proof.
  intros cs X Y k j H1 H2.
  assert (L1 : length (upd_bytes cs k X) = length cs) by (apply upd_bytes_length; lia).
  assert (L2 : length (upd_bytes X j Y) = length X) by (apply upd_bytes_length; lia).
  assert (L3 : length (upd_bytes (upd_bytes cs k X) (k + j) Y) = length cs)
    by (rewrite upd_bytes_length; [exact L1 | rewrite L1; lia]).
  assert (L4 : length (upd_bytes cs k (upd_bytes X j Y)) = length cs) by (apply upd_bytes_length; rewrite L2; lia).
  apply hb_nth_error_ext; [congruence|]. rewrite L3. intros i Hi.
  rewrite (upd_bytes_nth (upd_bytes cs k X) (k + j) Y i) by (rewrite ?L1; lia).
  rewrite (upd_bytes_nth cs k X i) by lia.
  rewrite (upd_bytes_nth cs k (upd_bytes X j Y) i) by (rewrite ?L2; lia).
  rewrite L2. hb_cases; try (exfalso; lia); try reflexivity.
  all: rewrite (upd_bytes_nth X j Y (i - k)) by lia; hb_cases; try (exfalso; lia); try reflexivity; f_equal; lia.
Qed.

Lemma hb_upd_same : forall (cs X Y : list byte) k, (k + length X <= length cs)%nat -> (length Y <= length X)%nat ->
  upd_bytes (upd_bytes cs k X) k Y = upd_bytes cs k (upd_bytes X 0 Y).
Proof.
  intros cs X Y k H1 H2. rewrite <- (hb_upd_nest cs X Y k 0) by (cbn; lia). rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma hb_upd_comm : forall (cs X1 X2 : list byte) k1 k2, (k1 + length X1 <= k2)%nat -> (k2 + length X2 <= length cs)%nat ->
  upd_bytes (upd_bytes cs k2 X2) k1 X1 = upd_bytes (upd_bytes cs k1 X1) k2 X2.
Proof.
  intros cs X1 X2 k1 k2 H1 H2.
  assert (L1 : length (upd_bytes cs k2 X2) = length cs) by (apply upd_bytes_length; lia).
  assert (L2 : length (upd_bytes cs k1 X1) = length cs) by (apply upd_bytes_length; lia).
  assert (L3 : length (upd_bytes (upd_bytes cs k2 X2) k1 X1) = length cs)
    by (rewrite upd_bytes_length; [exact L1 | rewrite L1; lia]).
  assert (L4 : length (upd_bytes (upd_bytes cs k1 X1) k2 X2) = length cs)
    by (rewrite upd_bytes_length; [exact L2 | rewrite L2; lia]).
  apply hb_nth_error_ext; [congruence|]. rewrite L3. intros i Hi.
  rewrite (upd_bytes_nth (upd_bytes cs k2 X2) k1 X1 i) by (rewrite ?L1; lia).
  rewrite (upd_bytes_nth cs k2 X2 i) by lia.
  rewrite (upd_bytes_nth (upd_bytes cs k1 X1) k2 X2 i) by (rewrite ?L2; lia).
  rewrite (upd_bytes_nth cs k1 X1 i) by lia.
  hb_cases; try (exfalso; lia); reflexivity.
Qed.

(** ** Memory *)
Lemma hb_bat_sub : forall m a (l : list byte) k n, bytes_at rsegs m a l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H].
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H as [H _].
  rewrite length_firstn, Nat.min_l in H by lia. exact H.
Qed.

Lemma hb_wr_sub : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H0 & H1 & H) Ha Hn Hl. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma hb_rw_cells : forall m a BS k len A W, bytes_at rsegs m a BS -> wr_at rsegs m a W ->
  (k + len <= length BS)%nat -> Z.of_nat (k + len) <= W -> A = a + Z.of_nat k ->
  rw_cells rsegs m A [CB len (firstn len (skipn k BS))].
Proof.
  intros m a BS k len A W HB HW Hk HKW ->. split.
  - split; [cbn [cells_wf cell_wf]; split; [rewrite length_firstn, length_skipn; lia | exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. apply hb_bat_sub; assumption.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. eapply hb_wr_sub; [exact HW | lia | lia | lia].
Qed.

Lemma hb_rw_bytes : forall m A len X, rw_cells rsegs m A [CB len X] -> bytes_at rsegs m A X.
Proof. intros m A len X [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

(** A write (a store or a callee) whose footprint is the range of X at A, inside the block BS at a. *)
Lemma hb_blk_upd : forall m m' a BS k X A W, bytes_at rsegs m a BS -> munch W m m' -> bytes_at rsegs m' A X ->
  A = a + Z.of_nat k -> (k + length X <= length BS)%nat -> sub_fp W [(A, A + Z.of_nat (length X))] ->
  bytes_at rsegs m' a (upd_bytes BS k X).
Proof.
  intros m m' a BS k X A W HB MU HX -> Hk SUB.
  apply (munch_weaken W _ m m' SUB) in MU.
  unfold upd_bytes.
  rewrite <- (firstn_skipn k BS) in HB. apply bytes_at_app in HB as [B1 B2].
  rewrite length_firstn, Nat.min_l in B2 by lia.
  rewrite <- (firstn_skipn (length X) (skipn k BS)) in B2. apply bytes_at_app in B2 as [_ B3].
  rewrite length_firstn, Nat.min_l in B3 by (rewrite length_skipn; lia).
  rewrite skipn_skipn, (Nat.add_comm (length X) k) in B3.
  apply bytes_at_app. split.
  - eapply bytes_at_transport; [exact B1 | exact MU |]. cbn [disjoint_from]. rewrite length_firstn, Nat.min_l by lia.
    split; [lia | exact I].
  - rewrite length_firstn, Nat.min_l by lia. apply bytes_at_app. split; [exact HX|].
    eapply bytes_at_transport; [exact B3 | exact MU |]. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma hb_pres_bytes : forall m a bs (x : word), bytes_at rsegs m a bs ->
  a <= bv_unsigned x < a + Z.of_nat (length bs) -> mrd rsegs m x <> None.
Proof.
  intros m a bs x (H0 & H1 & H) Hx.
  specialize (H (Z.to_nat (bv_unsigned x - a)) ltac:(lia)).
  replace (wa (a + Z.of_nat (Z.to_nat (bv_unsigned x - a)))) with x in H.
  - rewrite H. intros E. apply nth_error_None in E. lia.
  - unfold wa. rewrite Z2Nat.id by lia. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) by lia.
    symmetry. apply Z_to_bv_lit_self.
Qed.

Lemma hb_pres_stk : forall m lo hi (x : word), stk rsegs m lo hi -> lo <= bv_unsigned x < hi -> mrd rsegs m x <> None.
Proof.
  intros m lo hi x (_ & _ & H) Hx. destruct (H (bv_unsigned x) Hx) as [_ (b & Hb)].
  unfold wa in Hb. rewrite Z_to_bv_lit_self in Hb. rewrite Hb. discriminate.
Qed.

Lemma hb_not_out1 : forall a b x, ~ outside [(a, b)] x -> a <= x < b.
Proof.
  intros a b x H. cbn [outside] in H.
  destruct (Z_le_dec a x); destruct (Z_lt_dec x b); try lia; (exfalso; apply H; split; [lia | exact I]).
Qed.

Lemma hb_sub1 : forall a b a' b', a' <= a -> b <= b' -> sub_fp [(a, b)] [(a', b')].
Proof. intros a b a' b' H1 H2 x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I]. Qed.

Lemma hb_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi);
    [right; intros [H' _]; lia | left; split; [lia | exact H] ..].
Qed.

Lemma hb_task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd rsegs m x <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU P x b Hx.
  destruct (hb_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho) in Hx. exact (T x b Hx).
  - specialize (P x Ho). unfold mrd in P. destruct (m x) as [b0|] eqn:E.
    + exact (T x b0 E).
    + left. intros Hf. apply P. exact (MemNorm.seg_rom_unmapped rsegs x Hf).
Qed.

Lemma hb_stk_wr : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at rsegs m a n.
Proof. intros m lo hi a n (H0 & H1 & H) Ha Hn Hb. split; [lia|]. split; [lia|]. intros i Hi. apply (H (a + i)). lia. Qed.

Lemma hb_wr_store_ok : forall m a n b (j : nat), wr_at rsegs m a n -> a <= b -> b + Z.of_nat j <= a + n ->
  store_ok rsegs m (wa b) j = true.
Proof.
  intros m a n b j W H1 H2. pose proof (wr_at_store_ok rsegs m a n (b - a) j W ltac:(lia) ltac:(lia)) as S.
  replace (a + (b - a)) with b in S by lia. exact S.
Qed.

Lemma hb_rd : forall m a bs n, bytes_at rsegs m a bs -> length bs = n -> ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (a + Z.of_nat 0) with (a + 0) in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

Ltac hb_mem m' E := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => remember mm as m' eqn:E end.

(** ** The walk *)
Section Walk.
Variables (n : nat) (gp tp ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
  (lo c p line Sp : Z) (k0 : nat) (rest : list Z) (o : nat) (nm : list Z) (mc : mconf).
Hypothesis HT : H_MF_TAIL n.
Hypothesis HMF : m_find_contract.
Hypothesis HMS : memset_contract.
Hypothesis HMC : memcpy_contract.
Hypothesis HMR : m_refuse_contract.
Hypothesis HL : (length rest <= n)%nat.
Hypothesis HNE : rest <> [].
Hypothesis Hnm : (0 < length nm < 16)%nat.
Hypothesis Ho : (o + length nm <= length (mf_line rest))%nat.
Hypothesis Hfn : firstn (length nm) (skipn o rest) = nm.
Hypothesis HK0 : (k0 <= length (mc_kept mc))%nat.
Hypothesis Hl0 : 0 <= line.
Hypothesis Hl1 : line + Z.of_nat (length rest) <= 65535.
Hypothesis Hrf : mc_refused mc + Z.of_nat (length rest) < 2 ^ 32.
Hypothesis Hov : mc_overflow mc + Z.of_nat (length rest) < 2 ^ 32.
Hypothesis Hsp0 : bv_unsigned sp0 = Sp + 208.
Hypothesis Hlo : 0 <= lo.
Hypothesis Hlo1 : lo + 5952 <= Sp.
Hypothesis Hsp1 : Sp + 208 < 2 ^ 63.
Hypothesis Hsp16 : Sp mod 16 = 0.
Hypothesis Hcs : c + 9240 <= lo \/ Sp + 208 <= c.
Hypothesis Hc0 : 0 < c.
Hypothesis Hc1 : c + 9244 <= 2 ^ 64.
Hypothesis Hc16 : c mod 16 = 0.
Hypothesis Hp0 : 0 < p.
Hypothesis Hp1 : p + Z.of_nat (length rest) + 1 <= 2 ^ 64.
Hypothesis Hps : p + Z.of_nat (length rest) + 8 <= lo \/ Sp + 208 <= p.
Hypothesis Hpc : p + Z.of_nat (length rest) + 1 <= c \/ c + 9236 <= p.
Hypothesis Hnmb : Forall (fun x => 0 <= x < 256) nm.
Hypothesis Hnm0 : ~ In 0 nm.
Hypothesis Hgen : 0 <= mc_gen mc < 2 ^ 32.
Hypothesis HN32 : (length (mc_seg mc) <= 32)%nat.

Lemma hb_len1 : (1 <= length rest)%nat.
Proof. assert (length rest <> 0%nat) by (intros H; apply HNE; apply length_zero_iff_nil; exact H). lia. Qed.

Lemma hb_no : (o + length nm <= length rest)%nat.
Proof. destruct (mf_line_rest rest) as [[_ L]|[_ [_ L]]]; lia. Qed.

Definition hb_env (m : word -> option byte) (fc : bv 32) : Prop :=
  mf_ctx m fc (bv_unsigned sp0) Sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 /\
  mf_text m (bv_unsigned sp0) lo c p rest.

Definition hb_post (F : bvmap 5 word) (m : word -> option byte) (st : mconf * option nat) : machine_state -> Prop :=
  mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0 (mf_fin st line rest).

Lemma hb_env_parts : forall m fc, hb_env m fc ->
  wr_at rsegs m c SEG_M_SIZE /\ mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp0) /\ frm0 fc /\
  MemNorm.task_mem rsegs m /\ cell8 m (Sp + 0x10) (c + MC_N).
Proof.
  intros m fc [(_ & _ & _ & C10 & _ & _ & _ & _ & WR & _ & _ & (FRM & TM & _) & _ & _ & (ST & _) & MI) _].
  exact (conj WR (conj MI (conj ST (conj FRM (conj TM C10))))).
Qed.

Lemma hb_stack_ok : forall m fc d, hb_env m fc -> 0 <= d -> lo + d <= Sp -> stack_ok rsegs m lo Sp d.
Proof.
  intros m fc d [CX _] Hd1 Hd2. destruct CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (STK & _ & _ & SR) & _).
  split; [|split; [lia | split; [exact Hsp16 | intros a Ha; apply SR; lia]]].
  destruct (stk_split rsegs m lo Sp (bv_unsigned sp0) STK ltac:(lia)) as [S1 _]. exact S1.
Qed.

Lemma hb_c10 : forall m fc, hb_env m fc -> ov_read_bytes rsegs m (wa (Sp + 16)) 8 = Some (le8 (Z_to_bv 64 (c + 8192))).
Proof.
  intros m fc HE. destruct (hb_env_parts m fc HE) as (_ & _ & _ & _ & _ & C10).
  apply hb_rd; [exact C10 | apply length_le8].
Qed.

Lemma hb_env_tr : forall m m' fc W, hb_env m fc -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' lo (bv_unsigned sp0) -> sub_fp W [(lo, Sp); (Sp + 0x20, Sp + 0x68); (c, c + SEG_M_SIZE)] ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd rsegs m x <> None) -> hb_env m' fc.
Proof.
  intros m m' fc W HE MU WM MI ST SUB P.
  destruct (hb_env_parts m fc HE) as (_ & _ & _ & FRM & TM & _). destruct HE as [CX TX].
  split.
  - eapply mf_ctx_transport; [exact CX | exact MU | exact WM | exact MI | | exact FRM | exact ST | exact SUB].
    exact (hb_task_mem_munch W m m' TM MU P).
  - eapply mf_text_transport; [exact TX | exact MU |].
    intros x Hx. apply SUB. cbn [outside] in Hx |- *. rewrite Hsp0 in Hx. destruct Hx as (H1 & H2 & _).
    refine (conj _ (conj _ (conj H2 I))); lia.
Qed.

(** A store of j bytes at a, in the frame's scratch cells or in the block. *)
Definition hb_where (m : word -> option byte) (a : Z) (j : nat) : Prop :=
  (Sp + 0x20 <= a /\ a + Z.of_nat j <= Sp + 0x68) \/
  (exists BS, bytes_at rsegs m c BS /\ Z.of_nat (length BS) = SEG_M_SIZE /\ c <= a /\ a + Z.of_nat j <= c + SEG_M_SIZE).

Lemma hb_so : forall m fc a j, hb_env m fc -> hb_where m a j -> store_ok rsegs m (wa a) j = true.
Proof.
  intros m fc a j HE HW. destruct (hb_env_parts m fc HE) as (WR & _ & ST & _).
  destruct HW as [H|(BS & _ & _ & H)].
  - eapply hb_wr_store_ok; [eapply (hb_stk_wr m lo (bv_unsigned sp0) a (Z.of_nat j) ST) | |]; lia.
  - eapply hb_wr_store_ok; [exact WR | |]; unfold SEG_M_SIZE in *; lia.
Qed.

Lemma hb_store : forall m fc a bs (j : nat) m', hb_env m fc -> length bs = j -> hb_where m a j ->
  m' = write_to_mem m (wa a) bs ->
  hb_env m' fc /\ munch [(a, a + Z.of_nat j)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' a bs.
Proof.
  intros m fc a bs j m' HE Hj HW ->.
  pose proof (hb_so m fc a j HE HW) as SO.
  destruct (hb_env_parts m fc HE) as (WR & MI & ST & FRM & TM & _).
  assert (Ha : 0 <= a /\ a + Z.of_nat j <= 2 ^ 64) by (destruct HW as [H|(BS & _ & _ & H)]; unfold SEG_M_SIZE in *; lia).
  assert (MU : munch [(a, a + Z.of_nat j)] m (write_to_mem m (wa a) bs)).
  { apply munch_write; [apply munch_refl | lia | lia | cbn [inside]; left; lia]. }
  assert (WM : wmono rsegs m (write_to_mem m (wa a) bs)) by (apply wmono_write, wmono_refl).
  split; [|split; [exact MU | split; [exact WM | apply bytes_at_write_same; lia]]].
  eapply hb_env_tr; [exact HE | exact MU | exact WM | | | |].
  - apply mem_inv_store; [exact MI | rewrite Hj; exact SO].
  - apply stk_write; [exact ST | lia | lia].
  - intros x Hx. cbn [outside] in *. destruct Hx as (X1 & X2 & X3 & _).
    destruct HW as [H|(BS & _ & _ & H)]; unfold SEG_M_SIZE in *; (split; [lia | exact I]).
  - intros x Hx. apply hb_not_out1 in Hx. destruct HW as [H|(BS & HB & HLB & H)].
    + apply (hb_pres_stk m lo (bv_unsigned sp0) x ST). lia.
    + apply (hb_pres_bytes m c BS x HB). unfold SEG_M_SIZE in *. lia.
Qed.

Lemma hb_rebase : forall F F1 m m1 W st s, (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get F k) ->
  munch W m m1 -> wmono rsegs m m1 -> sub_fp W (M_FILE_W (bv_unsigned sp0) c k0 (mf_fin st line rest)) ->
  evt rsegs (hb_post F1 m1 st) s -> evt rsegs (hb_post F m st) s.
Proof. intros. unfold hb_post in *. eapply mf_post_back; eassumption. Qed.

Ltac hb_rb F1 m1 W := eapply (hb_rebase _ F1 _ m1 W).

Lemma hb_W_fr : forall st a b, Sp - 5952 <= a -> b <= Sp + 208 ->
  sub_fp [(a, b)] (M_FILE_W (bv_unsigned sp0) c k0 (mf_fin st line rest)).
Proof. intros st a b H1 H2. apply mf_W_frame; unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K; lia. Qed.

Lemma hb_W_seg : forall st gi a b, mf_cur_ok (fst st) (snd st) -> (gi < length (mc_seg (fst st)))%nat ->
  c + 256 * Z.of_nat gi <= a -> b <= c + 256 * Z.of_nat gi + 256 ->
  sub_fp [(a, b)] (M_FILE_W (bv_unsigned sp0) c k0 (mf_fin st line rest)).
Proof.
  intros st gi a b Hc Hg H1 H2. eapply sub_fp_trans; [|apply mf_W_fin; exact Hc].
  eapply sub_fp_trans; [|apply (mf_W_seg (bv_unsigned sp0) c k0 (fst st) gi 0 256 Hg); unfold MSEG_SIZE; lia].
  apply hb_sub1; unfold mseg_addr, MSEG_SIZE; lia.
Qed.

Lemma hb_W_cnt : forall st a b, mf_cur_ok (fst st) (snd st) -> c + 8192 <= a -> b <= c + 8204 ->
  sub_fp [(a, b)] (M_FILE_W (bv_unsigned sp0) c k0 (mf_fin st line rest)).
Proof.
  intros st a b Hc H1 H2. eapply sub_fp_trans; [|apply mf_W_fin; exact Hc].
  eapply sub_fp_trans; [|apply mf_W_counters]. apply hb_sub1; unfold MC_N, MC_REFUSED; lia.
Qed.

Lemma hb_W_ref : forall st mcr ln kn, mf_grows (m_refuse mcr ln kn) (fst st) -> mf_cur_ok (fst st) (snd st) ->
  (k0 <= length (mc_kept mcr))%nat ->
  sub_fp (m_refuse_W Sp c mcr) (M_FILE_W (bv_unsigned sp0) c k0 (mf_fin st line rest)).
Proof.
  intros st mcr ln kn Hg Hc Hk. eapply sub_fp_trans; [|apply mf_W_fin; exact Hc].
  eapply sub_fp_trans; [|apply mf_W_grows; exact Hg].
  apply mf_W_refuse; [unfold M_FILE_STACK, M_REFUSE_STACK, M_FILE_FRAME, PRINTF_K; lia | lia | exact Hk].
Qed.

(** The tail 0x143d4 with the line's result (mc', cur'). *)
Lemma hb_tail : forall m F fc mc' cur' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word),
  hb_env m fc -> mconf_at rsegs m c mc' -> cell8 m (Sp + 0x20) (cur_ptr c cur') -> cur_ok mc' cur' ->
  (k0 <= length (mc_kept mc'))%nat -> mc_refused mc' <= mc_refused mc + 1 -> mc_overflow mc' <= mc_overflow mc + 1 ->
  evt rsegs (hb_post F m (mc', cur'))
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 (Z_to_bv 64 9) (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
        F (Z_to_bv 64 0x143d4) fc None m (seg_rom rsegs)).
Proof.
  intros m F fc mc' cur' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 [CX TX] HM HC HO HK HR HV.
  unfold hb_post, mf_post, mf_fin.
  pose proof (mf_rest_lt rest HNE) as Hlt.
  eapply HT.
  - lia.
  - rewrite (unsigned_lit Sp) by lia. eapply mf_tail_loop with (p := p); try eassumption.
    + eapply mf_cnt_next; [exact HNE | exact Hrf | exact HR].
    + eapply mf_cnt_next; [exact HNE | exact Hov | exact HV].
  - unfold m_file_regs. repeat split.
Qed.

(** 0x14714: g->gen = c->gen for the entry i (found, after the optional refusal), then the tail. *)
Lemma hb_join : forall m F fc c1 i (ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t0 t1 t2 t3 t4 t5 t6 : word),
  hb_env m fc -> mconf_at rsegs m c c1 -> cell8 m (Sp + 0x20) (c + 256 * Z.of_nat i) ->
  (i < length (mc_seg c1))%nat -> (k0 <= length (mc_kept c1))%nat ->
  mc_refused c1 <= mc_refused mc + 1 -> mc_overflow c1 <= mc_overflow mc + 1 ->
  evt rsegs (hb_post F m (m_upd c1 i (ms_with_gen (mc_gen c1)), Some i))
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 (Z_to_bv 64 9) (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14714) fc None m (seg_rom rsegs)).
Proof.
  intros m F fc c1 i ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t0 t1 t2 t3 t4 t5 t6 HE HM HCUR Hi HK HR HV.
  pose proof HM as (BS & HB & HEn).
  pose proof (mconf_enc_bounds false c1 BS HEn) as (_ & HS32 & _ & Hg1 & _).
  pose proof HEn as (HLB & _).
  pose proof (hb_c10 m fc HE) as RD. step. clear RD.
  pose proof (mconf_rd_gen rsegs false m c c1 HM) as RD. unfold MC_GEN in RD. step. clear RD.
  pose proof (hb_rd m (Sp + 32) _ 8 HCUR (length_le8 _)) as RD. step. clear RD.
  assert (HW : hb_where m (c + 256 * Z.of_nat i + 252) 4).
  { right. exists BS. unfold SEG_M_SIZE in *. refine (conj HB (conj HLB (conj _ _))); lia. }
  pose proof (hb_so m fc _ 4 HE HW) as SO. step. clear SO.
  rewrite (hb_le4_sx32 (mc_gen c1)) by lia.
  hb_mem m2 E2.
  destruct (hb_store m fc _ _ 4 m2 HE (length_le4 _) HW E2) as (HE2 & MU2 & WM2 & BG). clear E2.
  assert (HM2 : mconf_at rsegs m2 c (m_upd c1 i (ms_with_gen (mc_gen c1)))).
  { exists (upd_bytes BS (256 * i + 252) (le4 (Z_to_bv 64 (mc_gen c1)))). split.
    - eapply hb_blk_upd; [exact HB | exact MU2 | exact BG | lia | rewrite length_le4; unfold SEG_M_SIZE in *; lia |].
      apply hb_sub1; rewrite ?length_le4; lia.
    - apply (mconf_enc_seg false c1 BS i (ms_with_gen (mc_gen c1)) 252 (le4 (Z_to_bv 64 (mc_gen c1))) HEn Hi).
      + rewrite length_le4. lia.
      + intros fb Hfb. exact (mseg_enc_gen _ fb (mc_gen c1) Hfb Hg1). }
  assert (HCUR2 : cell8 m2 (Sp + 0x20) (c + 256 * Z.of_nat i)).
  { unfold cell8 in *. eapply bytes_at_transport; [exact HCUR | exact MU2 |]. cbn [disjoint_from]. rewrite length_le8.
    split; [lia | exact I]. }
  assert (Hi2 : (i < length (mc_seg (m_upd c1 i (ms_with_gen (mc_gen c1)))))%nat).
  { unfold m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length. exact Hi. }
  hb_rb F m2 [(c + 256 * Z.of_nat i + 252, c + 256 * Z.of_nat i + 252 + Z.of_nat 4)];
    [intros; reflexivity | exact MU2 | exact WM2 | eapply (hb_W_seg _ i); [exact Hi2 | exact Hi2 | lia | lia] |].
  step.
  eapply hb_tail; [exact HE2 | exact HM2 | exact HCUR2 | exact Hi2 | exact HK | exact HR | exact HV].
Qed.

(** The new entry's model and cursor. *)
Definition hb_g0 : mseg := ms_with_gen (mc_gen mc) (mseg0 nm).

Lemma hb_new_ok : mf_cur_ok (m_set_segs mc (mc_seg mc ++ [hb_g0])) (Some (length (mc_seg mc))).
Proof. unfold mf_cur_ok, m_set_segs. cbn [mc_seg]. rewrite length_app. cbn [length]. lia. Qed.

(** The new path from 0x146e0 (n < 32): n++, memset, cur, memcpy, gen, tail. The block bytes BS at m1 encode mc. *)
Lemma hb_new : forall m1 F fc BS (ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
  hb_env m1 fc -> bytes_at rsegs m1 c BS -> mconf_enc mc BS -> (length (mc_seg mc) < 32)%nat ->
  evt rsegs (hb_post F m1 (m_set_segs mc (mc_seg mc ++ [hb_g0]), Some (length (mc_seg mc))))
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b)
             (Z_to_bv 64 (Z.of_nat (length (mc_seg mc)))) a1 (Z_to_bv 64 (c + 8192)) a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 (Z_to_bv 64 (p + Z.of_nat o))
             (Z_to_bv 64 (Z.of_nat (length nm))) (Z_to_bv 64 9) (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
        F (Z_to_bv 64 0x146e0) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 F fc BS ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 HE1 HB HEn HF.
  pose proof hb_len1 as HL1. pose proof hb_no as HNO.
  pose proof HEn as (HLB & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG & _).
  unfold SEG_M_SIZE in HLB.
  assert (GC1 : bytes_at rsegs m1 (c + 9136) (le4 (Z_to_bv 64 (mc_gen mc)))).
  { destruct HG as [_ HG]. pose proof (hb_bat_sub m1 c BS (Z.to_nat MC_GEN) 4 HB ltac:(unfold MC_GEN; lia)) as B.
    replace (c + Z.of_nat (Z.to_nat MC_GEN)) with (c + 9136) in B by (unfold MC_GEN; lia).
    rewrite <- HG. exact B. }
  (* 0x146e0 a1 = n + 1, 0x146e4 a0 = n << 8, 0x146e8 `sw a1, 0(a2)` *)
  do 2 step.
  assert (HW2 : hb_where m1 (c + 8192) 4).
  { right. exists BS. unfold SEG_M_SIZE. refine (conj HB (conj HLB (conj _ _))); lia. }
  pose proof (hb_so m1 fc _ 4 HE1 HW2) as SO. step. clear SO.
  hb_mem m2 E2.
  destruct (hb_store m1 fc _ (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc)) + 1))) 4 m2 HE1 (length_le4 _) HW2 E2)
    as (HE2 & MU2 & WM2 & BN). clear E2.
  assert (HB2 : bytes_at rsegs m2 c
                  (upd_bytes BS (Z.to_nat MC_N) (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc)) + 1))))).
  { eapply hb_blk_upd; [exact HB | exact MU2 | exact BN | unfold MC_N; lia | rewrite length_le4; unfold MC_N; lia |].
    apply hb_sub1; rewrite ?length_le4; lia. }
  set (BS1 := upd_bytes BS (Z.to_nat MC_N) (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc)) + 1)))) in *.
  assert (LB1 : length BS1 = length BS) by (apply upd_bytes_length; rewrite length_le4; unfold MC_N; lia).
  assert (GC2 : bytes_at rsegs m2 (c + 9136) (le4 (Z_to_bv 64 (mc_gen mc)))).
  { eapply bytes_at_transport; [exact GC1 | exact MU2 |]. cbn [disjoint_from]. rewrite length_le4. split; [lia | exact I]. }
  eapply (hb_rebase _ F _ m2 [(c + 8192, c + 8192 + Z.of_nat 4)]);
    [intros; reflexivity | exact MU2 | exact WM2 | apply hb_W_cnt; [exact hb_new_ok | lia | lia] |].
  clear MU2 WM2 GC1 BN.
  (* 0x146ec s4 = c + 256 n; a2 = 256, a0 = s4, a1 = 0; `jal memset` 0x146fc *)
  step.
  rewrite (hb_shl8 c (Z.of_nat (length (mc_seg mc)))) by lia.
  do 4 step.
  destruct (hb_env_parts m2 fc HE2) as (WR2 & MI2 & ST2 & _).
  eapply evt_cut.
  { eapply HMS.
    - rewrite !unsigned_lit by lia. change (Z.to_nat 256) with 256%nat.
      eapply (hb_rw_cells m2 c BS1 (256 * length (mc_seg mc)) 256); [exact HB2 | exact WR2 | | | ].
      + rewrite LB1. lia.
      + unfold SEG_M_SIZE. lia.
      + lia.
    - exact MI2. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3
              & MI3 & RW3).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !unsigned_lit in MU3, RW3 by lia.
  change (Z.to_nat 256) with 256%nat in RW3. change (0 mod 256) with 0 in RW3.
  pose proof (hb_rw_bytes _ _ _ _ RW3) as BZ. clear RW3.
  assert (HB3 : bytes_at rsegs m3 c (upd_bytes BS1 (256 * length (mc_seg mc)) (repeat ZERO 256))).
  { eapply hb_blk_upd; [exact HB2 | exact MU3 | exact BZ | lia | rewrite repeat_length, LB1; lia |].
    apply hb_sub1; rewrite ?repeat_length; lia. }
  set (BS2 := upd_bytes BS1 (256 * length (mc_seg mc)) (repeat ZERO 256)) in *.
  assert (LB2 : length BS2 = length BS) by (rewrite <- LB1; apply upd_bytes_length; rewrite repeat_length, LB1; lia).
  assert (ST3 : stk rsegs m3 lo (bv_unsigned sp0)).
  { eapply stk_transport_disjoint; [exact ST2 | exact MU3 | exact WM3 |]. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (HE3 : hb_env m3 fc).
  { eapply hb_env_tr; [exact HE2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 | |].
    - intros x Hx. cbn [outside] in *. destruct Hx as (_ & _ & H3 & _). unfold SEG_M_SIZE in *. split; [lia | exact I].
    - intros x Hx. apply hb_not_out1 in Hx. apply (hb_pres_bytes m2 c BS1 x HB2). rewrite LB1. lia. }
  assert (GC3 : bytes_at rsegs m3 (c + 9136) (le4 (Z_to_bv 64 (mc_gen mc)))).
  { eapply bytes_at_transport; [exact GC2 | exact MU3 |]. cbn [disjoint_from]. rewrite length_le4. split; [lia | exact I]. }
  eapply (hb_rebase _ F _ m3 [(c + 256 * Z.of_nat (length (mc_seg mc)),
                               c + 256 * Z.of_nat (length (mc_seg mc)) + 256)]);
    [intros; reflexivity | exact MU3 | exact WM3
    | eapply (hb_W_seg _ (length (mc_seg mc))); [exact hb_new_ok | exact hb_new_ok | lia | lia] |].
  clear MU3 WM3 MI3 BZ HB2 GC2 ST2 MI2 WR2 HE2.
  (* 0x14700 `sd s4, 0x20(sp)` *)
  assert (HW4 : hb_where m3 (Sp + 32) 8) by (left; lia).
  pose proof (hb_so m3 fc _ 8 HE3 HW4) as SO. step. clear SO.
  hb_mem m4 E4.
  destruct (hb_store m3 fc _ (le8 (Z_to_bv 64 (c + 256 * Z.of_nat (length (mc_seg mc))))) 8 m4 HE3 (length_le8 _)
              HW4 E4) as (HE4 & MU4 & WM4 & CUR4). clear E4.
  assert (HB4 : bytes_at rsegs m4 c BS2).
  { eapply bytes_at_transport; [exact HB3 | exact MU4 |]. cbn [disjoint_from]. rewrite LB2. split; [lia | exact I]. }
  assert (GC4 : bytes_at rsegs m4 (c + 9136) (le4 (Z_to_bv 64 (mc_gen mc)))).
  { eapply bytes_at_transport; [exact GC3 | exact MU4 |]. cbn [disjoint_from]. rewrite length_le4. split; [lia | exact I]. }
  eapply (hb_rebase _ F _ m4 [(Sp + 32, Sp + 32 + Z.of_nat 8)]);
    [intros; reflexivity | exact MU4 | exact WM4 | apply hb_W_fr; lia |].
  clear MU4 WM4 HB3 GC3 HE3.
  (* a0 = s4, a1 = nm, a2 = |nm|; `jal memcpy` 0x14710 *)
  do 4 step.
  destruct (hb_env_parts m4 fc HE4) as (WR4 & MI4 & ST4 & _).
  eapply evt_cut.
  { eapply HMC with (src := zb nm).
    - rewrite unsigned_lit by lia.
      pose proof (mf_text_bytes m4 _ lo c p rest o (length nm) (proj2 HE4) HNO) as B. rewrite Hfn in B. exact B.
    - rewrite unsigned_lit by lia. rewrite Nat2Z.id. apply hb_length_zb.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id.
      eapply (hb_rw_cells m4 c BS2 (256 * length (mc_seg mc)) (length nm)); [exact HB4 | exact WR4 | | | ].
      + rewrite LB2. lia.
      + unfold SEG_M_SIZE. lia.
      + lia.
    - rewrite !unsigned_lit by lia. lia.
    - exact MI4. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m5 & ->
              & MU5 & WM5 & MI5 & RW5 & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !unsigned_lit in MU5, RW5 by lia. rewrite Nat2Z.id in RW5.
  pose proof (hb_rw_bytes _ _ _ _ RW5) as BY. clear RW5.
  assert (HB5 : bytes_at rsegs m5 c (upd_bytes BS2 (256 * length (mc_seg mc)) (zb nm))).
  { eapply hb_blk_upd; [exact HB4 | exact MU5 | exact BY | lia | rewrite hb_length_zb, LB2; lia |].
    apply hb_sub1; rewrite ?hb_length_zb; lia. }
  set (BS3 := upd_bytes BS2 (256 * length (mc_seg mc)) (zb nm)) in *.
  assert (LB3 : length BS3 = length BS) by (rewrite <- LB2; apply upd_bytes_length; rewrite hb_length_zb, LB2; lia).
  assert (ST5 : stk rsegs m5 lo (bv_unsigned sp0)).
  { eapply stk_transport_disjoint; [exact ST4 | exact MU5 | exact WM5 |]. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (HE5 : hb_env m5 fc).
  { eapply hb_env_tr; [exact HE4 | exact MU5 | exact WM5 | exact MI5 | exact ST5 | |].
    - intros x Hx. cbn [outside] in *. destruct Hx as (_ & _ & H3 & _). unfold SEG_M_SIZE in *. split; [lia | exact I].
    - intros x Hx. apply hb_not_out1 in Hx. apply (hb_pres_bytes m4 c BS2 x HB4). rewrite LB2. lia. }
  assert (GC5 : bytes_at rsegs m5 (c + 9136) (le4 (Z_to_bv 64 (mc_gen mc)))).
  { eapply bytes_at_transport; [exact GC4 | exact MU5 |]. cbn [disjoint_from]. rewrite length_le4. split; [lia | exact I]. }
  assert (CUR5 : cell8 m5 (Sp + 32) (c + 256 * Z.of_nat (length (mc_seg mc)))).
  { unfold cell8. eapply bytes_at_transport; [exact CUR4 | exact MU5 |]. cbn [disjoint_from]. rewrite length_le8.
    split; [lia | exact I]. }
  eapply (hb_rebase _ F _ m5 [(c + 256 * Z.of_nat (length (mc_seg mc)),
                               c + 256 * Z.of_nat (length (mc_seg mc)) + Z.of_nat (length nm))]);
    [intros; reflexivity | exact MU5 | exact WM5
    | eapply (hb_W_seg _ (length (mc_seg mc))); [exact hb_new_ok | exact hb_new_ok | lia | lia] |].
  clear MU5 WM5 MI5 BY HB4 GC4 ST4 MI4 WR4 HE4 CUR4.
  (* 0x14714 `ld a0, 0x10(sp)`, `lw a0, 0x3b0(a0)`, `ld a1, 0x20(sp)`, `sw a0, 0xfc(a1)` *)
  pose proof (hb_c10 m5 fc HE5) as RD. step. clear RD.
  pose proof (hb_rd m5 (c + 9136) _ 4 GC5 (length_le4 _)) as RD. step. clear RD.
  pose proof (hb_rd m5 (Sp + 32) _ 8 CUR5 (length_le8 _)) as RD. step. clear RD.
  assert (HW6 : hb_where m5 (c + 256 * Z.of_nat (length (mc_seg mc)) + 252) 4).
  { right. exists BS3. unfold SEG_M_SIZE. refine (conj HB5 (conj _ (conj _ _))); [rewrite LB3; exact HLB | lia | lia]. }
  pose proof (hb_so m5 fc _ 4 HE5 HW6) as SO. step. clear SO.
  rewrite (hb_le4_sx32 (mc_gen mc)) by lia.
  hb_mem m6 E6.
  destruct (hb_store m5 fc _ _ 4 m6 HE5 (length_le4 _) HW6 E6) as (HE6 & MU6 & WM6 & BG). clear E6.
  assert (HB6 : bytes_at rsegs m6 c (upd_bytes BS3 (256 * length (mc_seg mc) + 252) (le4 (Z_to_bv 64 (mc_gen mc))))).
  { eapply hb_blk_upd; [exact HB5 | exact MU6 | exact BG | lia | rewrite length_le4, LB3; lia |].
    apply hb_sub1; rewrite ?length_le4; lia. }
  assert (CUR6 : cell8 m6 (Sp + 32) (c + 256 * Z.of_nat (length (mc_seg mc)))).
  { unfold cell8 in *. eapply bytes_at_transport; [exact CUR5 | exact MU6 |]. cbn [disjoint_from]. rewrite length_le8.
    split; [lia | exact I]. }
  eapply (hb_rebase _ F _ m6 [(c + 256 * Z.of_nat (length (mc_seg mc)) + 252,
                               c + 256 * Z.of_nat (length (mc_seg mc)) + 252 + Z.of_nat 4)]);
    [intros; reflexivity | exact MU6 | exact WM6
    | eapply (hb_W_seg _ (length (mc_seg mc))); [exact hb_new_ok | exact hb_new_ok | lia | lia] |].
  (* 0x14724 `j 0x143d4` *)
  step.
  eapply hb_tail; [exact HE6 | | exact CUR6 | exact hb_new_ok | exact HK0 | cbn [m_set_segs mc_refused]; lia
                  | cbn [m_set_segs mc_overflow]; lia].
  exists (upd_bytes BS3 (256 * length (mc_seg mc) + 252) (le4 (Z_to_bv 64 (mc_gen mc)))). split; [exact HB6|].
  assert (LE1 : length (upd_bytes (repeat ZERO 256) 0 (zb nm)) = 256%nat)
    by (rewrite upd_bytes_length; rewrite ?repeat_length, ?hb_length_zb; cbn; lia).
  assert (LE2 : length (upd_bytes (upd_bytes (repeat ZERO 256) 0 (zb nm)) 252 (le4 (Z_to_bv 64 (mc_gen mc)))) = 256%nat)
    by (rewrite upd_bytes_length; rewrite ?LE1, ?length_le4; lia).
  subst BS3 BS2 BS1.
  rewrite (hb_upd_same _ (repeat ZERO 256) (zb nm) (256 * length (mc_seg mc)))
    by (rewrite ?LB1, ?repeat_length, ?hb_length_zb; lia).
  rewrite (hb_upd_nest _ (upd_bytes (repeat ZERO 256) 0 (zb nm)) (le4 (Z_to_bv 64 (mc_gen mc)))
             (256 * length (mc_seg mc)) 252) by (rewrite ?LB1, ?LE1, ?length_le4; lia).
  rewrite (hb_upd_comm BS _ (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc)) + 1))) (256 * length (mc_seg mc))
             (Z.to_nat MC_N)) by (rewrite ?LE2, ?length_le4; unfold MC_N; lia).
  exact (mconf_enc_append false mc BS hb_g0 _ HEn HF (mseg_enc_new nm (mc_gen mc) ltac:(lia) Hnm0 Hnmb Hgen)).
Qed.

(** The whole sub-piece from 0x14488. *)
Lemma hb_walk : forall m F fc cur (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
  hb_env m fc -> mconf_at rsegs m c mc -> cell8 m (Sp + 0x20) (cur_ptr c cur) ->
  evt rsegs (hb_post F m (mh_find mc nm (line + 1)))
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 (Z_to_bv 64 (p + Z.of_nat o))
             (Z_to_bv 64 (Z.of_nat (length nm))) (Z_to_bv 64 9) (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14488) fc None m (seg_rom rsegs)).
Proof.
  intros m F fc cur ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 HE HM HCUR.
  pose proof hb_len1 as HL1. pose proof hb_no as HNO.
  destruct (hb_env_parts m fc HE) as (WR & MI & ST & FRM & TM & _).
  (* a0 = c, a1 = nm, a2 = |nm|; `jal m_find` 0x14494 *)
  do 4 step.
  eapply evt_cut.
  { eapply HMF with (l := zb nm) (lo := lo). unfold m_find_pre.
    rewrite !unsigned_lit by lia.
    refine (conj _ (conj Hc16 (conj HM (conj _ (conj _ (conj _ (conj _ (conj _ MI)))))))).
    - lia.
    - unfold apart, SEG_M_SIZE. lia.
    - pose proof (mf_text_bytes m _ lo c p rest o (length nm) (proj2 HE) HNO) as B. rewrite Hfn in B. exact B.
    - rewrite hb_length_zb. reflexivity.
    - unfold apart. lia.
    - apply (hb_stack_ok m fc); [exact HE | unfold M_FIND_STACK; lia | unfold M_FIND_STACK; lia]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1
              & MI1 & ST1 & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (unsigned_lit c) by lia. rewrite (hb_zs_zb nm Hnmb).
  rewrite (unsigned_lit Sp) in MU1, ST1 by lia. unfold M_FIND_STACK in MU1.
  assert (ST1' : stk rsegs m1 lo (bv_unsigned sp0)).
  { eapply mf_stk_after; [exact ST | exact MU1 | exact WM1 | exact ST1 | lia | cbn [disjoint_from]; split; [lia | exact I]]. }
  assert (HE1 : hb_env m1 fc).
  { eapply hb_env_tr; [exact HE | exact MU1 | exact WM1 | exact MI1 | exact ST1' | |].
    - intros x Hx. cbn [outside] in *. destruct Hx as (H1 & _). split; [lia | exact I].
    - intros x Hx. apply hb_not_out1 in Hx. apply (hb_pres_stk m lo (bv_unsigned sp0) x ST). lia. }
  assert (HM1 : mconf_atp rsegs false m1 c mc).
  { eapply mconf_atp_transport; [exact HM | exact MU1 |]. cbn [disjoint_from]. unfold SEG_M_SIZE. split; [lia | exact I]. }
  assert (HCUR1 : cell8 m1 (Sp + 0x20) (cur_ptr c cur)).
  { unfold cell8 in *. eapply bytes_at_transport; [exact HCUR | exact MU1 |]. cbn [disjoint_from]. rewrite length_le8.
    split; [lia | exact I]. }
  eapply (hb_rebase _ F _ m1 [(Sp - 48, Sp)]); [intros; reflexivity | exact MU1 | exact WM1 | apply hb_W_fr; lia |].
  clear MU1 WM1 MI1 ST1 ST1' HE HM HCUR WR MI ST FRM TM.
  pose proof (mconf_atp_bytes rsegs false m1 c mc HM1) as (BS & HB & HEn & _).
  pose proof HEn as (HLB & _ & _ & _ & [HOV _] & _).
  unfold mh_find, m_find_ptr. destruct (m_find mc nm) as [i|] eqn:Ef.
  - (* found: g = &seg[i] *)
    pose proof (m_find_lt mc nm i Ef) as Hi.
    pose proof (mconf_enc_bounds false mc BS HEn) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HSG).
    destruct (HSG i Hi) as (_ & _ & _ & Hgi).
    unfold mseg_addr, MSEG_SIZE.
    step.
    rewrite hb_eqb_lit by lia. rewrite (proj2 (Z.eqb_neq (c + 256 * Z.of_nat i) 0)) by lia. cbv iota.
    (* 0x1449c `sd a0, 0x20(sp)` *)
    assert (HW1 : hb_where m1 (Sp + 32) 8) by (left; lia).
    pose proof (hb_so m1 fc _ 8 HE1 HW1) as SO. step. clear SO.
    hb_mem m2 E2.
    destruct (hb_store m1 fc _ (le8 (Z_to_bv 64 (c + 256 * Z.of_nat i))) 8 m2 HE1 (length_le8 _) HW1 E2)
      as (HE2 & MU2 & WM2 & CUR2). clear E2.
    assert (HM2 : mconf_atp rsegs false m2 c mc).
    { eapply mconf_atp_transport; [exact HM1 | exact MU2 |]. cbn [disjoint_from]. unfold SEG_M_SIZE. split; [lia | exact I]. }
    eapply (hb_rebase _ F _ m2 [(Sp + 32, Sp + 32 + Z.of_nat 8)]);
      [intros; reflexivity | exact MU2 | exact WM2 | apply hb_W_fr; lia |].
    clear MU2 WM2.
    (* `lw a0, 0xfc(a0)`, `ld a1, 0x10(sp)`, `lw a1, 0x3b0(a1)`, `bne a0, a1` *)
    pose proof (mconf_rd_seg_gen rsegs false m2 c mc i HM2 Hi) as RD. unfold mseg_addr, MSEG_SIZE, MS_GEN in RD.
    step. clear RD.
    pose proof (hb_c10 m2 fc HE2) as RD. step. clear RD.
    pose proof (mconf_rd_gen rsegs false m2 c mc HM2) as RD. unfold MC_GEN in RD. step. clear RD.
    step.
    rewrite (hb_sx32_eqb _ _ Hgi Hgen).
    destruct (Z.eqb_spec (ms_gen (nth i (mc_seg mc) mseg_d)) (mc_gen mc)) as [Eg|Eg]; cbn [negb]; cbv iota.
    + (* g->gen == c->gen: m_refuse(c, line) 0x144b8, then 0x14714 *)
      do 3 step.
      eapply (mf_refuse_call HMR 0x144b8) with (mc := mc) (knock := false) (w := c + 256 * Z.of_nat i) (p := p)
        (rest := rest) (sp0 := bv_unsigned sp0) (lo := lo) (m := m2).
      * lia.
      * lia.
      * reflexivity.
      * rewrite unsigned_lit by lia. exact (proj1 HE2).
      * exact (proj2 HE2).
      * rewrite unsigned_lit by lia. exact CUR2.
      * exact HM2.
      * lia.
      * lia.
      * intros m3 F3 fc3 u0 u1 u2 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 CX3 TX3 CUR3 HM3 MU3 WM3 FR3.
        rewrite (unsigned_lit Sp) in CX3, CUR3, MU3 by lia.
        change (0x144b8 + 4) with 0x144bc.
        pose proof (m_refuse_sizes mc (line + 1) false) as (Es & Hk1 & _).
        eapply (hb_rebase _ F3 _ m3 (m_refuse_W Sp c mc)); [exact FR3 | exact MU3 | exact WM3 | |].
        { apply hb_W_ref with (ln := line + 1) (kn := false).
          - apply m_upd_grows.
          - unfold mf_cur_ok, m_upd, m_set_segs. cbn [fst snd mc_seg]. rewrite upd_nth_length, Es. exact Hi.
          - exact HK0. }
        step.
        eapply (hb_join m3 F3 fc3 (m_refuse mc (line + 1) false) i);
          [exact (conj CX3 TX3) | exact HM3 | exact CUR3 | rewrite Es; exact Hi | lia | | ].
        -- unfold m_refuse. cbv zeta. cbn [mc_refused]. lia.
        -- unfold m_refuse. cbv zeta. cbn [mc_overflow]. lia.
    + (* g->gen != c->gen: 0x14714 *)
      eapply (hb_join m2 F fc mc i); [exact HE2 | exact HM2 | exact CUR2 | exact Hi | exact HK0 | lia | lia].
  - (* not found *)
    step.
    rewrite hb_eqb_lit by lia. rewrite Z.eqb_refl. cbv iota.
    (* 0x14624 `ld a2, 0x10(sp)`, `lw a0, 0(a2)`, `blt a0, s11` *)
    pose proof (hb_c10 m1 fc HE1) as RD. step. clear RD.
    pose proof (mconf_rd_n rsegs false m1 c mc HM1) as RD. unfold MC_N in RD. step. clear RD.
    rewrite (hb_sx32_small (Z.of_nat (length (mc_seg mc)))) by lia.
    step. rewrite hb_lts_small by lia.
    destruct (Nat.leb_spec 32 (length (mc_seg mc))) as [HF|HF].
    + (* full: overflow++ 0x14638, m_refuse 0x14644, cur = NULL *)
      rewrite (proj2 (Z.ltb_ge (Z.of_nat (length (mc_seg mc))) 32)) by lia. cbv iota.
      pose proof (mconf_rd_overflow rsegs false m1 c mc HM1) as RD. unfold MC_OVERFLOW in RD. step. clear RD.
      step.
      assert (HW2 : hb_where m1 (c + 8196) 4).
      { right. exists BS. unfold SEG_M_SIZE in *. refine (conj HB (conj HLB (conj _ _))); lia. }
      pose proof (hb_so m1 fc _ 4 HE1 HW2) as SO. step. clear SO.
      rewrite (hb_le4_inc (mc_overflow mc)) by lia.
      hb_mem m2 E2.
      destruct (hb_store m1 fc _ _ 4 m2 HE1 (length_le4 _) HW2 E2) as (HE2 & MU2 & WM2 & BO). clear E2.
      assert (HM2 : mconf_atp rsegs false m2 c (mc_set_overflow (mc_overflow mc + 1) mc)).
      { exists (upd_bytes BS (Z.to_nat MC_OVERFLOW) (le4 (Z_to_bv 64 (mc_overflow mc + 1)))). split.
        - eapply hb_blk_upd; [exact HB | exact MU2 | exact BO | unfold MC_OVERFLOW; lia
                             | rewrite length_le4; unfold MC_OVERFLOW, SEG_M_SIZE in *; lia |].
          apply hb_sub1; rewrite ?length_le4; lia.
        - apply (mconf_enc_overflow false mc BS (mc_overflow mc + 1) HEn). lia. }
      assert (HCUR2 : cell8 m2 (Sp + 0x20) (cur_ptr c cur)).
      { unfold cell8 in *. eapply bytes_at_transport; [exact HCUR1 | exact MU2 |]. cbn [disjoint_from].
        rewrite length_le8. split; [lia | exact I]. }
      eapply (hb_rebase _ F _ m2 [(c + 8196, c + 8196 + Z.of_nat 4)]);
        [intros; reflexivity | exact MU2 | exact WM2 | apply hb_W_cnt; [exact I | lia | lia] |].
      clear MU2 WM2.
      do 3 step.
      eapply (mf_refuse_call HMR 0x14644) with (mc := mc_set_overflow (mc_overflow mc + 1) mc) (knock := false)
        (w := cur_ptr c cur) (p := p) (rest := rest) (sp0 := bv_unsigned sp0) (lo := lo) (m := m2).
      * lia.
      * lia.
      * reflexivity.
      * rewrite unsigned_lit by lia. exact (proj1 HE2).
      * exact (proj2 HE2).
      * rewrite unsigned_lit by lia. exact HCUR2.
      * exact HM2.
      * lia.
      * cbn [mc_set_overflow mc_refused]. lia.
      * intros m3 F3 fc3 u0 u1 u2 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 CX3 TX3 CUR3 HM3 MU3 WM3 FR3.
        rewrite (unsigned_lit Sp) in CX3, CUR3, MU3 by lia.
        change (0x14644 + 4) with 0x14648.
        eapply (hb_rebase _ F3 _ m3 (m_refuse_W Sp c (mc_set_overflow (mc_overflow mc + 1) mc)));
          [exact FR3 | exact MU3 | exact WM3 | |].
        { apply hb_W_ref with (ln := line + 1) (kn := false); [exact (mf_grows_refl _) | exact I | exact HK0]. }
        assert (HE3 : hb_env m3 fc3) by exact (conj CX3 TX3).
        assert (HW3 : hb_where m3 (Sp + 32) 8) by (left; lia).
        pose proof (hb_so m3 fc3 _ 8 HE3 HW3) as SO. step. clear SO.
        hb_mem m4 E4.
        destruct (hb_store m3 fc3 _ (le8 (Z_to_bv 64 0)) 8 m4 HE3 (length_le8 _) HW3 E4) as (HE4 & MU4 & WM4 & CUR4).
        clear E4.
        assert (HM4 : mconf_atp rsegs false m4 c (m_refuse (mc_set_overflow (mc_overflow mc + 1) mc) (line + 1) false)).
        { eapply mconf_atp_transport; [exact HM3 | exact MU4 |]. cbn [disjoint_from]. unfold SEG_M_SIZE.
          split; [lia | exact I]. }
        eapply (hb_rebase _ F3 _ m4 [(Sp + 32, Sp + 32 + Z.of_nat 8)]);
          [intros; reflexivity | exact MU4 | exact WM4 | apply hb_W_fr; lia |].
        step.
        pose proof (m_refuse_sizes (mc_set_overflow (mc_overflow mc + 1) mc) (line + 1) false) as (_ & Hk1 & _).
        eapply hb_tail; [exact HE4 | exact HM4 | exact CUR4 | exact I | | | ].
        -- unfold mc_set_overflow in Hk1. cbn [mc_kept] in Hk1. lia.
        -- unfold m_refuse. cbv zeta. cbn [mc_refused mc_set_overflow]. lia.
        -- unfold m_refuse. cbv zeta. cbn [mc_overflow mc_set_overflow]. lia.
    + (* new entry at n < 32 *)
      rewrite (proj2 (Z.ltb_lt (Z.of_nat (length (mc_seg mc))) 32)) by lia. cbv iota.
      exact (hb_new m1 F fc BS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE1 HB HEn HF).
Qed.

End Walk.

Theorem mf_hdrb_holds : m_find_contract -> memset_contract -> memcpy_contract -> m_refuse_contract -> S_MF_HDRB.
Proof.
  intros HMF HMS HMC HMR n HT. unfold H_MF_HFIND.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest o nm HL HNE HLP HR Hnm Ho Hfn E5 E6.
  destruct HR as (-> & -> & -> & -> & -> & -> & -> & -> & ->). subst s5 s6.
  apply mf_loop_iff in HLP. destruct HLP as (CX & TX & HM & HCUR & _ & HK0 & Hl0 & Hl1 & Hrf & Hov).
  pose proof CX as CXb. apply mf_ctx_bounds in CXb. destruct CXb as (_ & Hst & Hs63 & _ & Hsp16 & Hcs & Hc0 & Hc1).
  pose proof CX as (E0 & _ & _ & _ & _ & _ & Hc16 & _ & _ & _ & _ & _ & _ & _ & ((Hlo & _) & _) & _).
  pose proof TX as TXb. apply mf_text_props in TXb. destruct TXb as (Hn0 & Hbyt & Hp0 & Hp1 & _).
  pose proof TX as (_ & _ & _ & Hps & Hpc).
  assert (Hspan : Z.of_nat (length rest) + 1 <= cstr_span p rest).
  { unfold cstr_span. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)). lia. }
  assert (Hin : forall x, In x nm -> In x rest).
  { intros x Hx. rewrite <- Hfn in Hx.
    assert (Hs : In x (skipn o rest))
      by (rewrite <- (firstn_skipn (length nm) (skipn o rest)); apply in_or_app; left; exact Hx).
    rewrite <- (firstn_skipn o rest). apply in_or_app. right. exact Hs. }
  assert (Hnmb : Forall (fun x => 0 <= x < 256) nm).
  { apply Forall_forall. intros x Hx. rewrite Forall_forall in Hbyt. exact (Hbyt x (Hin x Hx)). }
  assert (Hnm0 : ~ In 0 nm) by (intros H0; exact (Hn0 (Hin 0 H0))).
  pose proof HM as (bs & _ & HEn).
  pose proof (mconf_enc_bounds false mc bs HEn) as (_ & HN32 & _ & Hgen & _).
  unfold apart in Hps, Hpc. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K, SEG_M_SIZE in *.
  rewrite <- (Z_to_bv_lit_self sp).
  pose proof (u64_range sp) as Rsp.
  eapply hb_walk; try eassumption; try (unfold hb_env; split; assumption); try lia.
Qed.
