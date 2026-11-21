(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PreOmega.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk AllocSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.IK Require Import ZSysLite ZCall ZCallL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac zlia_div := Z.to_euclidean_division_equations; lia.

Definition zfupd (f : Z -> Z) (i v : Z) : Z -> Z :=
  fun j => if Z.eqb j i then v else f j.

Lemma zfupd_same : forall f i v, zfupd f i v i = v.
Proof. intros. unfold zfupd. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma zfupd_other : forall f i v j, j <> i -> zfupd f i v j = f j.
Proof. intros f i v j H. unfold zfupd. rewrite (proj2 (Z.eqb_neq j i) H). reflexivity. Qed.

Definition cell_mod (k : Z) : Z := 2 ^ (8 * k).

Lemma Z_to_le_bytes_mod_cell : forall (k : Z) z, 0 <= k ->
  Z_to_le_bytes (Z.to_nat k) (z mod cell_mod k) = Z_to_le_bytes (Z.to_nat k) z.
Proof.
  intros k z Hk. unfold cell_mod.
  replace (z mod 2 ^ (8 * k)) with (bv_wrap (Z.to_N (8 * k)) z).
  - apply Z_to_le_bytes_wrap. lia.
  - unfold bv_wrap, bv_modulus. f_equal. f_equal. lia.
Qed.


Definition mem_arr (k : Z) (segs : list Segment) (M : mem) (base n : Z) (f : Z -> Z) : Prop :=
  0 <= base /\ 0 <= n /\ 0 < k /\ base + k * n <= two64 /\
  forall i, 0 <= i < n -> mem_is segs M (base + k * i) (Z_to_le_bytes (Z.to_nat k) (f i)).

Section Basic.
Variable segs : list Segment.

Lemma mem_arr_bounds : forall k M base n f,
  mem_arr k segs M base n f -> 0 <= base /\ 0 <= n /\ 0 < k /\ base + k * n <= two64.
Proof. intros k M base n f (A & B & C & D & _). auto. Qed.

Lemma mem_arr_get : forall k M base n f i,
  mem_arr k segs M base n f -> 0 <= i < n ->
  mem_is segs M (base + k * i) (Z_to_le_bytes (Z.to_nat k) (f i)).
Proof. intros k M base n f i (_ & _ & _ & _ & H) Hi. apply H. exact Hi. Qed.

Lemma mem_arr_rdn : forall k M base n f i a,
  mem_arr k segs M base n f -> 0 <= i < n -> a = base + k * i ->
  rdn segs M (w64 a) (Z.to_nat k) = Some (Z_to_le_bytes (Z.to_nat k) (f i)).
Proof.
  intros k M base n f i a H Hi ->. pose proof (mem_arr_get k M base n f i H Hi) as E.
  unfold mem_is in E. rewrite length_Z_to_le_bytes in E. exact E.
Qed.

Lemma mem_arr32_get : forall M base n f i,
  mem_arr 4 segs M base n f -> 0 <= i < n -> mem_u32 segs M (base + 4 * i) (f i).
Proof. intros. eapply mem_arr_get in H; eauto. Qed.
Lemma mem_arr64_get : forall M base n f i,
  mem_arr 8 segs M base n f -> 0 <= i < n -> mem_u64 segs M (base + 8 * i) (f i).
Proof. intros. eapply mem_arr_get in H; eauto. Qed.

Lemma mem_arr_ext : forall k M base n f g,
  mem_arr k segs M base n f -> (forall i, 0 <= i < n -> f i = g i) -> mem_arr k segs M base n g.
Proof.
  intros k M base n f g (A & B & C & D & H) E. repeat split; try assumption.
  intros i Hi. rewrite <- (E i Hi). apply H. exact Hi.
Qed.

Lemma mem_arr_ext_mod : forall k M base n f g,
  mem_arr k segs M base n f -> (forall i, 0 <= i < n -> f i mod cell_mod k = g i mod cell_mod k) ->
  mem_arr k segs M base n g.
Proof.
  intros k M base n f g (A & B & C & D & H) E. repeat split; try assumption.
  intros i Hi. rewrite <- (Z_to_le_bytes_mod_cell k (g i)), <- (E i Hi), Z_to_le_bytes_mod_cell by lia.
  apply H. exact Hi.
Qed.

Lemma mem_arr_nil : forall k M base f, 0 <= base <= two64 -> 0 < k -> mem_arr k segs M base 0 f.
Proof. intros k M base f Hb Hk. repeat split; try lia. Qed.

Lemma mem_arr_of_elems : forall k M base n f,
  0 <= base -> 0 <= n -> 0 < k -> base + k * n <= two64 ->
  (forall i, 0 <= i < n -> mem_is segs M (base + k * i) (Z_to_le_bytes (Z.to_nat k) (f i))) ->
  mem_arr k segs M base n f.
Proof. intros. repeat split; assumption. Qed.



Lemma mem_arr8_of_bytes : forall M base (bs : list byte),
  mem_is segs M base bs -> 0 <= base -> base + Z.of_nat (length bs) <= two64 ->
  mem_arr 1 segs M base (Z.of_nat (length bs)) (fun i => bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
Proof.
  intros M base bs H Hb Hn. repeat split; try lia.
  intros i Hi. unfold mem_is. change (Z.to_nat 1) with 1%nat. cbn [Z_to_le_bytes length].
  rewrite Z_to_bv_bv_unsigned. replace (base + 1 * i) with (base + i) by lia.
  apply (mem_is_byte segs M base bs i H). lia.
Qed.

Definition le_cell (k : Z) (bs : list byte) (i : Z) : Z :=
  bytes_le_to_Z (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs)).

Lemma lor_shiftl8_mod : forall (b : byte) z, 0 <= z ->
  Z.lor (bv_unsigned b) (Z.shiftl z 8) mod 256 = bv_unsigned b.
Proof.
  intros b z Hz. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.lor_spec.
  destruct (Z.ltb_spec n 8).
  - rewrite Z.ones_spec_low, Z.shiftl_spec_low by lia. rewrite Bool.orb_false_r, Bool.andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r.
    symmetry. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [->|]; [cbn; lia|].
    apply (Z.lt_le_trans _ 8); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2^8) with 256. lia.
Qed.

Lemma lor_shiftl8_shiftr : forall (b : byte) z, 0 <= z ->
  Z.shiftr (Z.lor (bv_unsigned b) (Z.shiftl z 8)) 8 = z.
Proof.
  intros b z Hz. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
  replace (Z.shiftr (bv_unsigned b) 8) with 0; [apply Z.lor_0_l|].
  symmetry. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (2^8) with 256. lia.
Qed.

Lemma bytes_roundtrip : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bytes_le_to_Z_nonneg bs) as Hz. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    apply lor_shiftl8_mod. exact Hz.
  - rewrite lor_shiftl8_shiftr by exact Hz. exact IH.
Qed.

Lemma bytes_roundtrip_len : forall bs k, length bs = k -> Z_to_le_bytes k (bytes_le_to_Z bs) = bs.
Proof. intros bs k <-. apply bytes_roundtrip. Qed.

Lemma mem_arr_of_bytes : forall k M base n (bs : list byte),
  mem_is segs M base bs -> 0 < k -> 0 <= n -> Z.of_nat (length bs) = k * n ->
  0 <= base -> base + k * n <= two64 ->
  mem_arr k segs M base n (le_cell k bs).
Proof.
  intros k M base n bs H Hk Hn Hlen Hb Hbn. repeat split; try lia.
  intros i Hi. unfold le_cell, mem_is.
  assert (Hsub := mem_is_sub segs M base bs (k * i) (Z.to_nat k) H ltac:(nia) ltac:(nia)).
  assert (L : length (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs)) = Z.to_nat k).
  { rewrite length_firstn, length_skipn. nia. }
  rewrite (bytes_roundtrip_len _ _ L). rewrite L. exact Hsub.
Qed.

Lemma mem_arr_split : forall k M base n f m,
  mem_arr k segs M base n f -> 0 <= m <= n ->
  mem_arr k segs M base m f /\ mem_arr k segs M (base + k * m) (n - m) (fun j => f (m + j)).
Proof.
  intros k M base n f m (A & B & C & D & H) Hm. split.
  - repeat split; try lia; try nia. intros i Hi. apply H. lia.
  - repeat split; try nia. intros i Hi.
    replace (base + k * m + k * i) with (base + k * (m + i)) by lia. apply H. lia.
Qed.

Lemma mem_arr_join : forall k M base n m f g,
  mem_arr k segs M base m f -> mem_arr k segs M (base + k * m) (n - m) g -> 0 <= m <= n ->
  mem_arr k segs M base n (fun j => if j <? m then f j else g (j - m)).
Proof.
  intros k M base n m f g (A & B & C & D & H) (A' & B' & C' & D' & H') Hm. repeat split; try nia.
  intros i Hi. destruct (Z.ltb_spec i m).
  - apply H. lia.
  - replace (base + k * i) with (base + k * m + k * (i - m)) by lia. apply H'. lia.
Qed.

Lemma mem_arr_sub : forall k M base n f lo len,
  mem_arr k segs M base n f -> 0 <= lo -> 0 <= len -> lo + len <= n ->
  mem_arr k segs M (base + k * lo) len (fun j => f (lo + j)).
Proof.
  intros k M base n f lo len H Hlo Hlen Hhi.
  destruct (mem_arr_split k M base n f lo H ltac:(lia)) as [_ H2].
  destruct (mem_arr_split k M _ _ _ len H2 ltac:(lia)) as [H3 _]. exact H3.
Qed.

Fixpoint zseq (s : Z) (n : nat) : list Z :=
  match n with O => [] | S n' => s :: zseq (s + 1) n' end.

Lemma zseq_length : forall s n, length (zseq s n) = n.
Proof. intros s n. revert s. induction n; intros; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.

Lemma mem_arr8_mem_is : forall M base n f,
  mem_arr 1 segs M base n f ->
  mem_is segs M base (map (fun j => Z_to_bv 8 (f j)) (zseq 0 (Z.to_nat n))).
Proof.
  intros M base n f (A & B & C & D & H).
  assert (G : forall (m : nat) s, 0 <= s -> s + Z.of_nat m <= n ->
            mem_is segs M (base + s) (map (fun j => Z_to_bv 8 (f j)) (zseq s m))).
  { induction m as [|m IH]; intros s Hs Hm.
    - unfold mem_is. reflexivity.
    - cbn [zseq map]. change (Z_to_bv 8 (f s) :: ?r) with ([Z_to_bv 8 (f s)] ++ r).
      apply mem_is_app.
      + replace (base + s) with (base + 1 * s) by lia. apply (H s). lia.
      + lazymatch goal with |- mem_is _ _ ?a _ => replace a with (base + (s + 1)) by (cbn; lia) end.
        apply IH; lia.
      + lia.
      + cbn [length]. rewrite length_map, zseq_length. lia. }
  replace base with (base + 0) by lia. apply G; lia.
Qed.

End Basic.

Section Stores.
Variable segs : list Segment.

Lemma mem_arr_upd : forall k M base n f a i v,
  mem_arr k segs M base n f -> a = base + k * i -> 0 <= i < n ->
  mem_arr k segs (wbytes M (w64 a) (Z_to_le_bytes (Z.to_nat k) v)) base n (zfupd f i v).
Proof.
  intros k M base n f a i v (A & B & C & D & H) -> Hi. repeat split; try assumption.
  intros j Hj. unfold zfupd. destruct (Z.eqb_spec j i) as [->|Hne].
  - apply mem_is_stored; rewrite ?length_Z_to_le_bytes; nia.
  - apply mem_is_frame; [apply H; exact Hj|].
    unfold zdisj. rewrite !length_Z_to_le_bytes. nia.
Qed.

Lemma mem_arr_frame : forall k M base n f a bs,
  mem_arr k segs M base n f ->
  zdisj a (Z.of_nat (length bs)) base (k * n) ->
  mem_arr k segs (wbytes M (w64 a) bs) base n f.
Proof.
  intros k M base n f a bs (A & B & C & D & H) Hd. repeat split; try assumption.
  intros j Hj. apply mem_is_frame; [apply H; exact Hj|].
  destruct Hd as (D1 & D2 & D3 & D4 & D5). unfold zdisj. rewrite length_Z_to_le_bytes. nia.
Qed.





Lemma mem_arr_magree : forall k M0 M lo1 hi1 lo2 hi2 base n f,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_arr k segs M0 base n f ->
  (base + k * n <= lo1 \/ hi1 <= base) -> (base + k * n <= lo2 \/ hi2 <= base) ->
  mem_arr k segs M base n f.
Proof.
  intros k M0 M lo1 hi1 lo2 hi2 base n f HA (A & B & C & D & H) H1 H2. repeat split; try assumption.
  intros j Hj. eapply mem_is_magree; [exact HA | apply H; exact Hj | nia | rewrite length_Z_to_le_bytes; nia | |];
    rewrite length_Z_to_le_bytes; nia.
Qed.

Lemma mem_arr_magreeL : forall k M0 M rs base n f,
  magreeL M0 M rs -> mem_arr k segs M0 base n f -> disj_all base (k * n) rs ->
  mem_arr k segs M base n f.
Proof.
  intros k M0 M rs base n f HA (A & B & C & D & H) Hd. repeat split; try assumption.
  intros j Hj. eapply mem_is_magreeL; [exact HA | apply H; exact Hj | nia | rewrite length_Z_to_le_bytes; nia |].
  rewrite length_Z_to_le_bytes.
  clear HA H. induction rs as [|[lo len] rs IH]; cbn in *; [exact I|].
  destruct Hd as [Hd1 Hd2]. split; [nia | apply IH; exact Hd2].
Qed.


End Stores.

Section Loads.
Variable segs : list Segment.

Lemma bytes_le_cell : forall k v, 0 <= k <= 8 ->
  bytes_le_to_Z (Z_to_le_bytes (Z.to_nat k) v) = v mod cell_mod k.
Proof.
  intros k v Hk. rewrite bytes_le_Z_to_le_any by lia. unfold cell_mod. f_equal. f_equal. lia.
Qed.

Lemma zu_ld_arr : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 8 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 8 * i -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (f i) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  eapply zu_ld_u64; [exact F | exact E | exact D | exact Hh | | exact Hk].
  rewrite Heq. exact (mem_arr64_get segs M base n f i Ha Hi).
Qed.

Lemma zu_lwu_arr : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 4 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 4 * i -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (f i mod two32) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  eapply zu_lwu_u32; [exact F | exact E | exact D | exact Hh | | exact Hk].
  rewrite Heq. exact (mem_arr32_get segs M base n f i Ha Hi).
Qed.

Lemma zu_lw_arr : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 4 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 4 * i -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bv_swrap 32 (f i)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  eapply zu_lw_u32; [exact F | exact E | exact D | exact Hh | | exact Hk].
  rewrite Heq. exact (mem_arr32_get segs M base n f i Ha Hi).
Qed.

Lemma zu_lhu_arr : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 2 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 2 * i -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (f i mod 65536) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  eapply zu_lhu; [exact F | exact E | exact D | exact Hh | |].
  - rewrite Heq. apply (mem_arr_rdn segs 2 M base n f i _ Ha Hi eq_refl).
  - rewrite (bytes_le_cell 2) by lia. exact Hk.
Qed.

Lemma swrap16_mod : forall v, bv_swrap 16 (v mod 65536) = bv_swrap 16 v.
Proof. intros. change (v mod 65536) with (bv_wrap 16 v). apply bv_swrap_wrap. Qed.

Lemma zu_lh_arr : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 2 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 2 * i -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bv_swrap 16 (f i)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  eapply zu_lh; [exact F | exact E | exact D | exact Hh | |].
  - rewrite Heq. apply (mem_arr_rdn segs 2 M base n f i _ Ha Hi eq_refl).
  - rewrite (bytes_le_cell 2), swrap16_mod by lia. exact Hk.
Qed.

Lemma zu_lbu_arr : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 1 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 1 * i -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (f i mod 256) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  eapply zu_lbu; [exact F | exact E | exact D | exact Hh | |].
  - rewrite Heq. apply (mem_arr_rdn segs 1 M base n f i _ Ha Hi eq_refl).
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact Hk.
Qed.

Lemma swrap8_mod : forall v, bv_swrap 8 (v mod 256) = bv_swrap 8 v.
Proof. intros. change (v mod 256) with (bv_wrap 8 v). apply bv_swrap_wrap. Qed.

Lemma zu_lb_arr : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 1 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 1 * i -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bv_swrap 8 (f i)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  eapply zu_lb; [exact F | exact E | exact D | exact Hh | |].
  - rewrite Heq. apply (mem_arr_rdn segs 1 M base n f i _ Ha Hi eq_refl).
  - unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite swrap8_mod. exact Hk.
Qed.

Lemma zu_lbu_arr' : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 1 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 1 * i -> 0 <= i < n ->
  0 <= f i < 256 ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (f i) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hr Hk.
  eapply zu_lbu_arr; try eassumption. rewrite Z.mod_small by exact Hr. exact Hk.
Qed.

Lemma zu_lhu_arr' : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 2 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 2 * i -> 0 <= i < n ->
  0 <= f i < 65536 ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (f i) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hr Hk.
  eapply zu_lhu_arr; try eassumption. rewrite Z.mod_small by exact Hr. exact Hk.
Qed.

Lemma zu_lh_arr' : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 2 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 2 * i -> 0 <= i < n ->
  -32768 <= f i < 32768 ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (f i) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hr Hk.
  eapply zu_lh_arr; try eassumption.
  rewrite bv_swrap_small by (change (bv_half_modulus 16) with 32768; lia). exact Hk.
Qed.

Lemma zu_lwu_arr' : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 4 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 4 * i -> 0 <= i < n ->
  0 <= f i < two32 ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (f i) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hr Hk.
  eapply zu_lwu_arr; try eassumption. rewrite Z.mod_small by exact Hr. exact Hk.
Qed.

Lemma zu_lw_arr' : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 4 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 4 * i -> 0 <= i < n ->
  -2147483648 <= f i < 2147483648 ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (f i) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hr Hk.
  eapply zu_lw_arr; try eassumption. rewrite swrap32_small by lia. exact Hk.
Qed.

End Loads.
