(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/L_hkit.v, with its module paths and module names changed; 801 of its 858 lines of code are new or changed and 196 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/reac_served_unmark_all.v; 487 of its 587 lines of code are new or changed and 758 lines of the source are left out. *)
(* reac_served_mark (reac_served_mark.c:48-92), PLAIN build: the memory, FILE, table, model and
   printf-argument facts the walk in lib/Prog/reac_served_mark.v uses. No address of the code here;
   the image facts are read by vm_compute over `rsegs`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c printf_facts_c
  mk_str mk_marks link_msgs_fit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YP09 YI04 YO0f YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The image's segments, readability, task_mem
   ========================================================================== *)

Lemma find_segment_out : forall segs lo hi x n,
  forallb (fun s => (lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi)) segs
    = true ->
  0 < n -> x < lo \/ hi <= x -> find_segment segs x n = None.
Proof.
  induction segs as [|s segs IH]; intros lo hi x n Hb Hn Hx; [reflexivity|].
  cbn [forallb] in Hb. apply andb_prop in Hb as [Hs Hr]. apply andb_prop in Hs as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base s)) x);
    destruct (Z.leb_spec (x + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb];
    try (exfalso; lia); eapply IH; eauto.
Qed.

(* every loaded segment of the plain image lies inside [IMG_LO, IMG_TOP) *)
Lemma seg_outside : forall x, x < IMG_LO \/ IMG_TOP <= x -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx. apply (find_segment_out rsegs IMG_LO IMG_TOP); [vm_compute; reflexivity | lia | exact Hx].
Qed.

(* outside every segment, a writable byte is a byte of the memory map, so it reads *)
Lemma stk_of_wr_out : forall m a n, wr_at rsegs m a n -> 0 <= n ->
  (a + n <= IMG_LO \/ IMG_TOP <= a) -> stk rsegs m a (a + n).
Proof.
  intros m a n (Ha & Hn & Hw) H0 Hout. split; [lia|]. split; [lia|].
  intros x Hx. pose proof (Hw (x - a) ltac:(lia)) as W. replace (a + (x - a)) with x in W by lia.
  split; [exact W|].
  unfold mrd. destruct (m (wa x)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply W. unfold wview. rewrite E. rewrite wa_unsigned by lia. rewrite seg_outside by lia.
  reflexivity.
Qed.

Lemma le8_bytes_rt : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite Z_to_le_bytes_mod by (cbn; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma guard_rom : forall i, (i < 8)%nat -> exists b, seg_rom rsegs (wa (A_GUARD + Z.of_nat i)) = Some b.
Proof.
  intros i Hi. do 8 (destruct i as [|i]; [vm_compute; eexists; reflexivity|]). lia.
Qed.

(* the stack protector's guard word is in .bss, which reads (0 when the map has no byte there) *)
Lemma guard_any : forall m, exists c : word, bytes_at rsegs m A_GUARD (le8 c).
Proof.
  intros m.
  set (g := fun i : nat =>
    match mrd rsegs m (wa (A_GUARD + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  exists (le_bytes_to_word (map g (seq 0 8))).
  rewrite le8_bytes_rt by (rewrite length_map, length_seq; reflexivity).
  split; [unfold A_GUARD; lia|]. split; [rewrite length_map, length_seq; unfold A_GUARD; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, nth_error_seq.
  replace (i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  cbn [option_map Nat.add]. unfold g.
  destruct (mrd rsegs m (wa (A_GUARD + Z.of_nat i))) as [b|] eqn:E; [reflexivity|].
  exfalso. unfold mrd in E. destruct (m (wa (A_GUARD + Z.of_nat i))); [discriminate|].
  destruct (guard_rom i Hi) as [b Hb]. rewrite Hb in E. discriminate.
Qed.

(* a stack above the image that task_mem covers lies below TASK_SIZE *)
Lemma sp_task : forall m lo hi, task_mem rsegs m -> stk rsegs m lo hi -> IMG_TOP <= lo -> lo < hi ->
  hi <= TASK_SIZE.
Proof.
  intros m lo hi T (H1 & H2 & H) Hl Hlh.
  destruct (H (hi - 1) ltac:(lia)) as [_ (b & Hb)].
  unfold mrd in Hb.
  assert (Hu : bv_unsigned (wa (hi - 1)) = hi - 1) by (apply wa_unsigned; lia).
  destruct (m (wa (hi - 1))) as [b'|] eqn:E.
  - destruct (T _ _ E) as [Hf|Ht].
    + exfalso. apply Hf. rewrite Hu. apply seg_outside. lia.
    + rewrite Hu in Ht. lia.
  - rewrite seg_rom_unmapped in Hb; [discriminate|]. rewrite Hu. apply seg_outside. lia.
Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z.le_gt_cases lo x) as [H1|H1]; [destruct (Z.lt_ge_cases x hi) as [H2|H2]|].
    + right. intros [Hn _]. lia.
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
  - right. intros [_ Ho]. exact (H Ho).
Qed.

Lemma task_mem_munch : forall W m m', task_mem rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> x < TASK_SIZE) -> task_mem rsegs m'.
Proof.
  intros W m m' T M H a b E. destruct (outside_dec W (bv_unsigned a)) as [Ho|Hn].
  - rewrite (M a Ho) in E. exact (T a b E).
  - right. apply H; [apply u64_range | exact Hn].
Qed.

Lemma munch_sym : forall W m m', munch W m m' -> munch W m' m.
Proof. intros W m m' H x Hx. symmetry. apply H, Hx. Qed.

(* ==========================================================================
   2. The memory FILE
   ========================================================================== *)

Lemma disjoint_sub : forall W a n b k, disjoint_from W a n -> a <= b -> b + k <= a + n -> disjoint_from W b k.
Proof.
  induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n b k D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia | eapply IH; eauto].
Qed.

Lemma vm_munch : forall W m m' a n v, munch W m m' -> disjoint_from W a (Z.of_nat n) -> 0 <= a ->
  a + Z.of_nat n <= 2 ^ 64 -> YI04.val_mem rsegs m a n v -> YI04.val_mem rsegs m' a n v.
Proof.
  intros W m m' a n v M D H0 H1 Hv k Hk. rewrite <- (Hv k Hk). unfold YP09.mbyte.
  rewrite M; [reflexivity|]. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia].
Qed.

Lemma memfile_k_transport : forall W m m' f k, memfile_k m f k -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W f MemFile.MF_BLOCK -> memfile_k m' f k.
Proof.
  intros W m m' f k (Hat & Hwin & Hwf & Hws & Hpl) M Wm D.
  pose proof Hat as (Hf0 & Hf1 & _).
  assert (HV : forall off n v, 0 <= off -> off + Z.of_nat n <= MemFile.MF_BLOCK ->
    mf_fld m f off n v -> mf_fld m' f off n v).
  { intros off n v H0 H1 Hv. unfold mf_fld in *. eapply vm_munch; [exact M | | lia | lia | exact Hv].
    eapply disjoint_sub; [exact D | lia | lia]. }
  split; [|split; [|split; [|split]]].
  - eapply MemFile.memfile_at_frame; [|exact Hat]. intros x Hx. unfold YP09.mbyte.
    rewrite M; [reflexivity|]. unfold MemFile.MF_ZEROED, MemFile.MF_BLOCK in *.
    rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia].
  - destruct Hwin as [(-> & H1 & H2 & H3) | (Hk & H1 & H2 & H3)]; [left | right];
      repeat split; try lia;
      (apply HV; [lia | unfold MemFile.MF_BLOCK; cbn; lia | assumption]).
  - eapply wr_at_transport; eassumption.
  - eapply wr_at_transport; eassumption.
  - exact Hpl.
Qed.

Lemma nth_error_zle : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma le_byte_bv8 : forall v w k,
  Z_to_bv 8 (YO0f.le_byte v w k) = Z_to_bv 8 (Z.shiftr (v mod 2 ^ (8 * Z.of_nat w)) (8 * Z.of_nat k)).
Proof.
  intros v w k. unfold YO0f.le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* a field fixes its value modulo its width *)
Lemma val_mem_mod : forall m a n v1 v2, YI04.val_mem rsegs m a n v1 -> YI04.val_mem rsegs m a n v2 ->
  v1 mod 2 ^ (8 * Z.of_nat n) = v2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros m a n v1 v2 H1 H2.
  assert (Hp : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
  assert (E : Z_to_le_bytes n (v1 mod 2 ^ (8 * Z.of_nat n)) = Z_to_le_bytes n (v2 mod 2 ^ (8 * Z.of_nat n))).
  { apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k n) as [Hk|Hk].
    - rewrite !nth_error_zle by exact Hk. rewrite <- !le_byte_bv8.
      pose proof (H1 k Hk) as B1. pose proof (H2 k Hk) as B2. rewrite B1 in B2. exact B2.
    - rewrite !(proj2 (nth_error_None _ _)) by (rewrite length_Z_to_le_bytes; lia). reflexivity. }
  pose proof (f_equal bytes_le_to_Z E) as E2.
  rewrite !bytes_le_to_Z_to_le_bytes in E2 by (apply Z.mod_pos_bound; exact Hp).
  rewrite !Z.mod_mod in E2 by lia. exact E2.
Qed.

Lemma mf_top : forall f, 0 < f -> f + MemFile.MF_BLOCK <= 2 ^ 64 -> f mod 16 = 0 -> f + 1304 < 2 ^ 64.
Proof.
  intros f H0 H1 H2. unfold MemFile.MF_BLOCK in H1.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity. rewrite P64 in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma memfile_k_unique : forall m f k1 k2, memfile_k m f k1 -> memfile_k m f k2 -> k1 = k2.
Proof.
  intros m f k1 k2 (Hat & W1 & _) (_ & W2 & _).
  destruct Hat as (Hf0 & Hf1 & Hf16 & _).
  pose proof (mf_top f Hf0 Hf1 Hf16) as Ht.
  destruct W1 as [(-> & A1 & B1 & C1) | (K1 & A1 & B1 & C1)];
    destruct W2 as [(-> & A2 & B2 & C2) | (K2 & A2 & B2 & C2)];
    unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ in *.
  - reflexivity.
  - exfalso. pose proof (val_mem_mod _ _ _ _ _ C1 C2) as E. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in E.
    rewrite Z.mod_0_l in E by lia. rewrite Z.mod_small in E by lia. lia.
  - exfalso. pose proof (val_mem_mod _ _ _ _ _ C1 C2) as E. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in E.
    rewrite Z.mod_0_l in E by lia. rewrite Z.mod_small in E by lia. lia.
  - pose proof (val_mem_mod _ _ _ _ _ B1 B2) as E. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in E.
    rewrite !Z.mod_small in E by lia. lia.
Qed.

(* what fprintf's Pre takes of the FILE, from memfile_k *)
Lemma memfile_k_dyn : forall m f k, memfile_k m f k ->
  exists fl om wend wpos wbase pos len pb,
    mf_dyn m f fl om wend wpos wbase pos len /\ mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k.
Proof.
  intros m f k (Hat & Hwin & Hwf & _ & Hpl).
  destruct Hat as (Hf0 & Hf1 & Hf16 & _ & Hfl & Hom & _ & Hc).
  pose proof (mf_top f Hf0 Hf1 Hf16) as Ht.
  assert (Hk : 0 <= k <= MemFile.MF_BUFSIZ)
    by (destruct Hwin as [(-> & _) | (H & _)]; [unfold MemFile.MF_BUFSIZ; lia | exact H]).
  assert (Hst : stk rsegs m f (f + MemFile.MF_BLOCK))
    by (apply stk_of_wr_out; [exact Hwf | unfold MemFile.MF_BLOCK; lia | exact Hpl]).
  destruct (stk_split rsegs m f (f + MemFile.MF_BUF) (f + MemFile.MF_BLOCK) Hst
    ltac:(unfold MemFile.MF_BUF, MemFile.MF_BLOCK; lia)) as [_ S1].
  destruct (stk_split rsegs m (f + MemFile.MF_BUF) (f + MemFile.MF_BUF + k) (f + MemFile.MF_BLOCK) S1
    ltac:(unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *; lia)) as [S2 _].
  destruct (stk_bytes rsegs m _ _ S2 ltac:(lia)) as (pb & Lpb & Bpb).
  assert (FL : exists fl, 0 <= fl < 2 ^ 32 /\ mf_fld m f 0 4 fl).
  { destruct Hfl as [H|H]; [exists MemFile.F_NORD | exists (MemFile.F_NORD + MemFile.F_ERR)];
      (split; [unfold MemFile.F_NORD, MemFile.F_ERR; lia | exact H]). }
  assert (OM : exists om, 0 <= om < 2 ^ 32 /\ mf_fld m f 136 4 om).
  { destruct Hom as [H|H]; [exists 0 | exists YI14.U32M1];
      (split; [unfold YI14.U32M1; lia | exact H]). }
  assert (WN : exists wend wpos wbase, 0 <= wend < 2 ^ 64 /\ 0 <= wpos < 2 ^ 64 /\ 0 <= wbase < 2 ^ 64 /\
     mf_fld m f 32 8 wend /\ mf_fld m f 40 8 wpos /\ mf_fld m f 56 8 wbase).
  { assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
    destruct Hwin as [(_ & A & B & C) | (_ & A & B & C)];
      [exists 0, 0, 0 |
       exists (f + MemFile.MF_BUF + MemFile.MF_BUFSIZ), (f + MemFile.MF_BUF + k), (f + MemFile.MF_BUF)];
      unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ in *; (split; [lia|]); (split; [lia|]); (split; [lia|]);
      (split; [exact A|]); (split; [exact B | exact C]). }
  destruct Hc as (pos & len & Hpl0 & Hls & Hpos & Hlen).
  change (MemFile.mf_size MemFile.link_mf) with 4096 in Hls.
  destruct FL as (fl & Rfl & Ffl). destruct OM as (om & Rom & Fom).
  destruct WN as (wend & wpos & wbase & R1 & R2 & R3 & F1 & F2 & F3).
  exists fl, om, wend, wpos, wbase, pos, len, pb.
  split; [|split; [exact Bpb | rewrite Lpb; lia]].
  unfold mf_dyn, SAID_SIZE.
  split; [exact Rfl|]. split; [exact Rom|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split; [lia|]. split; [lia|].
  split; [exact Ffl|]. split; [exact Fom|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
  split; [exact Hpos | exact Hlen].
Qed.

(* ==========================================================================
   3. The fake kernel, the interface table, the marks block, strings
   ========================================================================== *)

Lemma nlk_transport : forall W m m' kbs, nlk_at m kbs -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W A_G_NL NK_SIZE -> nlk_at m' kbs.
Proof.
  intros W m m' kbs [U L] M Wm D. split; [|exact L].
  eapply u8arr_transport; [exact U | exact M | exact Wm | rewrite L; exact D].
Qed.

Lemma nlk_unique : forall m k1 k2, nlk_at m k1 -> nlk_at m k2 -> k1 = k2.
Proof.
  intros m k1 k2 [[B1 _] L1] [[B2 _] L2]. eapply bytes_at_unique; [exact B1 | exact B2 | lia].
Qed.

Lemma marks_transport : forall W m m' a gbs, marks_at m a gbs -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W a MK_SIZE -> marks_at m' a gbs.
Proof.
  intros W m m' a gbs [U L] M Wm D. split; [|exact L].
  eapply u8arr_transport; [exact U | exact M | exact Wm | rewrite L; exact D].
Qed.

Lemma marks_unique : forall m a g1 g2, marks_at m a g1 -> marks_at m a g2 -> g1 = g2.
Proof.
  intros m a g1 g2 [[B1 _] L1] [[B2 _] L2]. eapply bytes_at_unique; [exact B1 | exact B2 | lia].
Qed.

Lemma cstr_transport : forall W m m' a s, cstr_at m a s -> munch W m m' ->
  disjoint_from W a (Z.of_nat (length s) + 1) -> cstr_at m' a s.
Proof.
  intros W m m' a s [B N] M D. split; [|exact N].
  eapply bytes_at_transport; [exact B | exact M |].
  replace (Z.of_nat (length (s ++ [zb 0]))) with (Z.of_nat (length s) + 1)
    by (rewrite length_app; cbn [length]; lia).
  exact D.
Qed.

Lemma u64_back : forall W m m' a v, u64_at m' a v -> munch W m m' -> disjoint_from W a 8 -> u64_at m a v.
Proof.
  intros W m m' a v B M D. eapply bytes_at_transport; [exact B | apply munch_sym; exact M |].
  rewrite length_le8. exact D.
Qed.

Lemma iftab_transport : forall W m m' kbs tab, iftab_at m kbs tab -> munch W m m' ->
  disjoint_from W (A_G_NL + NK_IF_NAME) (NK_SIZE - NK_IF_NAME) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> disjoint_from W p (Z.of_nat (length n2) + 1)) ->
  iftab_at m' kbs tab.
Proof.
  intros W m m' kbs tab (Hn & Hl & H) M D Hs.
  split; [exact Hn|]. split; [exact Hl|].
  intros i nm ix Hi. destruct (H i nm ix Hi) as (Hix & p & Hp & Hp0 & Hc & Hx).
  assert (Li : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  split; [exact Hix|]. exists p. split; [|split; [exact Hp0|split]].
  - eapply bytes_at_transport; [exact Hp | exact M |]. rewrite length_le8.
    eapply disjoint_sub; [exact D | |]; unfold NK_IF_NAME, NK_SIZE in *; lia.
  - eapply cstr_transport; [exact Hc | exact M | exact (Hs i nm ix p Hi Hp)].
  - eapply bytes_at_transport; [exact Hx | exact M |]. rewrite length_le4.
    eapply disjoint_sub; [exact D | |]; unfold NK_IF_NAME, NK_IF_INDEX, NK_SIZE in *; lia.
Qed.

Lemma u64_unique : forall m a p1 p2, u64_at m a p1 -> u64_at m a p2 -> wz p1 = wz p2.
Proof.
  intros m a p1 p2 H1 H2.
  pose proof (bytes_at_unique m a _ _ H1 H2 ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 (wz p1)), <- (le_bytes_to_word_le8 (wz p2)), E. reflexivity.
Qed.

Lemma iftab_unique : forall m kbs t1 t2, iftab_at m kbs t1 -> iftab_at m kbs t2 -> t1 = t2.
Proof.
  intros m kbs t1 t2 (N1 & _ & H1) (N2 & _ & H2).
  assert (L : length t1 = length t2) by lia.
  apply nth_error_ext. intros i.
  destruct (nth_error t1 i) as [[n1 ix1]|] eqn:E1.
  - assert (Li : (i < length t2)%nat) by (rewrite <- L; apply nth_error_Some; rewrite E1; discriminate).
    destruct (nth_error t2 i) as [[n2 ix2]|] eqn:E2; [|apply nth_error_None in E2; lia].
    destruct (H1 i n1 ix1 E1) as (R1 & p1 & P1 & _ & C1 & X1).
    destruct (H2 i n2 ix2 E2) as (R2 & p2 & P2 & _ & C2 & X2).
    pose proof (u64_unique _ _ _ _ P1 P2) as Ep.
    assert (Ep' : p1 = p2).
    { destruct C1 as [B1 _]. destruct C2 as [B2 _].
      pose proof (bytes_at_bound _ _ _ _ B1) as Q1. pose proof (bytes_at_bound _ _ _ _ B2) as Q2.
      rewrite length_app in Q1, Q2. cbn [length] in Q1, Q2.
      apply (f_equal bv_unsigned) in Ep. unfold wz in Ep. rewrite !unsigned_lit in Ep by lia. exact Ep. }
    subst p2. rewrite (cstr_at_unique m n1 p1 n2 C1 C2).
    assert (Ex : ix1 = ix2).
    { assert (P31 : 2 ^ 31 = 2147483648) by reflexivity. assert (P32 : 2 ^ 32 = 4294967296) by reflexivity.
      assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
      pose proof (bytes_at_unique m _ _ _ X1 X2 ltac:(rewrite !length_le4; reflexivity)) as E.
      unfold le4, wz in E. apply (f_equal bytes_le_to_Z) in E.
      rewrite !bytes_le_to_Z_to_le_bytes in E
        by (pose proof (u64_range (Z_to_bv 64 ix1)); pose proof (u64_range (Z_to_bv 64 ix2)); lia).
      rewrite !unsigned_lit in E by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in E.
      rewrite !Z.mod_small in E by lia. exact E. }
    subst ix2. reflexivity.
  - apply nth_error_None in E1. symmetry. apply nth_error_None. lia.
Qed.

(* ==========================================================================
   4. The model
   ========================================================================== *)

Lemma talk_after_kept : forall K, k_chunks (talk_after K) = k_chunks K /\ k_end (talk_after K) = k_end K.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [split; reflexivity|].
  destruct (negb (k_send K =? 0)); [split; reflexivity|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  destruct v; split; reflexivity.
Qed.

Lemma read_core_state : forall tab nm kc ac reqs K,
  k_chunks (r_state (read_core tab nm kc ac reqs K)) = k_chunks K
  /\ k_end (r_state (read_core tab nm kc ac reqs K)) = k_end K.
Proof.
  intros tab nm kc ac reqs K. unfold read_core. cbv zeta.
  destruct nm as [s|]; [|split; reflexivity].
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|].
  exact (talk_after_kept K).
Qed.

Lemma write_core_state : forall tab nm al reqs K,
  k_chunks (w_state (write_core tab nm al reqs K)) = k_chunks K
  /\ k_end (w_state (write_core tab nm al reqs K)) = k_end K.
Proof.
  intros tab nm al reqs K. unfold write_core. cbv zeta.
  destruct nm as [s|]; [|split; reflexivity].
  destruct al as [a|]; [|split; reflexivity].
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|].
  exact (talk_after_kept K).
Qed.

Lemma kstate_of : forall kbs S, nk_chunks kbs = k_chunks S -> nk_next kbs = Z.of_nat (k_next S) ->
  nk_end_errno kbs = k_end S -> nk_socket_errno kbs = k_sock S -> nk_send_errno kbs = k_send S ->
  nk_kstate kbs = S.
Proof.
  intros kbs K H1 H2 H3 H4 H5. destruct K as [c n e so se].
  cbn [k_chunks k_next k_end k_sock k_send] in *.
  unfold nk_kstate. rewrite H1, H2, H3, H4, H5, Nat2Z.id. reflexivity.
Qed.

Lemma rd32s_range : forall c off, - 2 ^ 31 <= rd32s c off < 2 ^ 31.
Proof.
  intros c off. unfold rd32s, rd32, rdn. cbv zeta.
  assert (L : (length (slice c off 4) <= 4)%nat) by (unfold slice; rewrite length_firstn; lia).
  pose proof (bytes_le_to_Z_nonneg (slice c off 4)) as H0.
  pose proof (bytes_le_to_Z_bound (slice c off 4)) as H1.
  assert (H2 : 2 ^ (8 * Z.of_nat (length (slice c off 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  assert (P31 : 2 ^ 31 = 2147483648) by reflexivity. assert (P32 : 2 ^ 32 = 4294967296) by reflexivity.
  destruct (Z.ltb_spec (bytes_le_to_Z (slice c off 4)) (2 ^ 31)); lia.
Qed.

Lemma msg_scan_err : forall f c off left code, msg_scan f c off left = NlErr code ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction f as [|f IH]; intros c off left code H; cbn [msg_scan] in H; [discriminate|].
  repeat match type of H with context [if ?b then _ else _] => destruct b end;
    try discriminate; try (injection H as <-; apply rd32s_range); eapply IH; exact H.
Qed.

Lemma chunk_loop_err : forall f cs i code j, chunk_loop f cs i = (NlErr code, j) ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction f as [|f IH]; intros cs i code j H; cbn [chunk_loop] in H; [discriminate|].
  destruct (nth_error cs i) as [c|]; [|discriminate].
  destruct (chunk_walk c) eqn:E; try discriminate.
  - eapply IH; exact H.
  - injection H as <- _. unfold chunk_walk in E. eapply msg_scan_err; exact E.
Qed.

Lemma talk_rc_range : forall K, 0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 31 <= talk_rc_lib K < 2 ^ 31.
Proof.
  intros K H1 H2 H3. assert (P31 : 2 ^ 31 = 2147483648) by reflexivity.
  unfold talk_rc_lib, talk_core.
  destruct (negb (k_sock K =? 0)); cbn [fst]; [lia|].
  destruct (negb (k_send K =? 0)); cbn [fst]; [lia|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j] eqn:E.
  destruct v; cbn [fst]; [lia | unfold E_IO; lia | eapply chunk_loop_err; exact E | lia].
Qed.

Lemma read_rc_range : forall tab nm kc ac reqs K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 31 <= r_rc (read_core tab nm kc ac reqs K) < 2 ^ 31.
Proof.
  intros tab nm kc ac reqs K H1 H2 H3. assert (P31 : 2 ^ 31 = 2147483648) by reflexivity.
  unfold read_core. cbv zeta.
  destruct nm as [s|]; [|cbn [r_rc]; unfold E_INVAL; lia].
  destruct (Nat.eqb (length s) 0); [cbn [r_rc]; unfold E_INVAL; lia|].
  destruct (index_of tab s =? 0); [cbn [r_rc]; unfold E_NODEV; lia|].
  cbn [r_rc]. apply talk_rc_range; assumption.
Qed.

Lemma write_rc_range : forall tab nm al reqs K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 31 <= w_rc (write_core tab nm al reqs K) < 2 ^ 31.
Proof.
  intros tab nm al reqs K H1 H2 H3. assert (P31 : 2 ^ 31 = 2147483648) by reflexivity.
  unfold write_core. cbv zeta.
  destruct nm as [s|]; [|cbn [w_rc]; unfold E_INVAL; lia].
  destruct al as [a|]; [|cbn [w_rc]; unfold E_INVAL; lia].
  destruct (Nat.eqb (length s) 0); [cbn [w_rc]; unfold E_INVAL; lia|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)); [cbn [w_rc]; unfold E_NAMETOOLONG; lia|].
  destruct (index_of tab s =? 0); [cbn [w_rc]; unfold E_NODEV; lia|].
  cbn [w_rc]. apply talk_rc_range; assumption.
Qed.

Lemma decide_cases : forall k a, decide k a = 0 \/ decide k a = 1 \/ decide k a = 2 \/ decide k a = 3.
Proof.
  intros k a. destruct (link_spec.decide_cases k a) as [H|[H|[H|H]]]; rewrite H;
    unfold V_MARK, V_OURS, V_LEAVE_VLAN, V_LEAVE_HOST; lia.
Qed.

Lemma text_of_attr_len : forall o cap, 1 <= cap -> Z.of_nat (length (text_of_attr o cap)) <= cap - 1.
Proof.
  intros o cap Hc. destruct o as [pay|]; cbn [text_of_attr].
  - apply cut_text_len; exact Hc.
  - cbn [length Z.of_nat]. lia.
Qed.

(* the nlk_wf bounds as the kstate reads them *)
Lemma kstate_bounds : forall kbs, nlk_wf kbs ->
  0 <= k_sock (nk_kstate kbs) < 2 ^ 31 /\ 0 <= k_send (nk_kstate kbs) < 2 ^ 31
  /\ 0 <= k_end (nk_kstate kbs) < 2 ^ 31.
Proof.
  intros kbs H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & He & Hs & Hd & _).
  unfold nk_kstate; cbn [k_sock k_send k_end]. lia.
Qed.

Lemma nk_sent_length : forall kbs, nlk_wf kbs -> nk_n_sent kbs = Z.of_nat (length (nk_sent kbs)).
Proof.
  intros kbs H. destruct H as (_ & _ & Hs & _). unfold nk_sent. rewrite length_map, length_seq. lia.
Qed.

Lemma nk_next_kstate : forall kbs, nlk_wf kbs -> nk_next kbs = Z.of_nat (k_next (nk_kstate kbs)).
Proof.
  intros kbs H. destruct H as (_ & Hn & _). unfold nk_kstate; cbn [k_next]. lia.
Qed.

Lemma mk_n_names : forall gbs, marks_wf gbs -> mk_n gbs = Z.of_nat (length (mk_names gbs)).
Proof. intros gbs [H _]. rewrite mk_names_length. lia. Qed.

(* ==========================================================================
   5. bcmp(alias, "reac-pw:served", 15) over the alias buffer
   ========================================================================== *)

(* bcmp over a buffer whose first bytes are a C string: it stops at the first difference, which comes at
   the latest at the string's NUL or at the policy string's NUL *)
Lemma memcmp_walk_junk : forall p s junk, ~ In (zb 0) s -> ~ In (zb 0) p ->
  firstn (S (length s)) junk = s ++ [zb 0] -> (S (length p) <= length junk)%nat ->
  exists v, memcmp_model junk (p ++ [zb 0]) (S (length p)) = Some v /\ - 256 < v < 256
            /\ (v = 0 <-> s = p).
Proof.
  induction p as [|b p IH]; intros s junk Ns Np Hj Lj.
  - destruct junk as [|j junk]; [cbn in Lj; lia|].
    destruct s as [|a s].
    + cbn [length firstn app] in Hj. injection Hj as Ej. subst j.
      exists 0. split; [cbn [app memcmp_model]; rewrite Z.eqb_refl; reflexivity|].
      split; [lia | split; intros _; reflexivity].
    + cbn [length firstn app] in Hj. injection Hj as Ej _. subst j.
      assert (Ha : bv_unsigned a <> 0) by (intros E; apply Ns; left; apply byte_zero; exact E).
      pose proof (byte_range a) as Ra.
      exists (bv_unsigned a - bv_unsigned (zb 0)). split.
      * cbn [app memcmp_model length].
        replace (bv_unsigned a =? bv_unsigned (zb 0)) with false; [reflexivity|].
        symmetry. apply Z.eqb_neq. rewrite bz_zb0. exact Ha.
      * rewrite bz_zb0. split; [lia|]. split; [lia | discriminate].
  - assert (Hb : bv_unsigned b <> 0) by (intros E; apply Np; left; apply byte_zero; exact E).
    pose proof (byte_range b) as Rb.
    destruct junk as [|j junk]; [cbn in Lj; lia|].
    destruct s as [|a s].
    + cbn [length firstn app] in Hj. injection Hj as Ej. subst j.
      exists (bv_unsigned (zb 0) - bv_unsigned b). split.
      * cbn [app memcmp_model length].
        replace (bv_unsigned (zb 0) =? bv_unsigned b) with false; [reflexivity|].
        symmetry. apply Z.eqb_neq. rewrite bz_zb0. lia.
      * rewrite bz_zb0. split; [lia|]. split; [lia | discriminate].
    + cbn [length firstn app] in Hj. injection Hj as Ej Hj. subst j.
      assert (Ha : bv_unsigned a <> 0) by (intros E; apply Ns; left; apply byte_zero; exact E).
      pose proof (byte_range a) as Ra.
      destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Eab|Nab].
      * apply byte_eq in Eab. subst b.
        destruct (IH s junk (fun H => Ns (or_intror H)) (fun H => Np (or_intror H)) Hj
          ltac:(cbn [length] in Lj; lia)) as (v & Hv & Rv & Iv).
        exists v. split.
        -- cbn [app memcmp_model length]. rewrite Z.eqb_refl. exact Hv.
        -- split; [exact Rv|]. rewrite Iv.
           split; [intros ->; reflexivity | intros H; injection H as H; exact H].
      * exists (bv_unsigned a - bv_unsigned b). split.
        -- cbn [app memcmp_model length].
           replace (bv_unsigned a =? bv_unsigned b) with false by (symmetry; apply Z.eqb_neq; exact Nab).
           reflexivity.
        -- split; [lia|]. split; [lia | intros H; injection H as H _; subst b; contradiction].
Qed.

Lemma bcmp_served : forall (al junk : list byte), ~ In (zb 0) al ->
  firstn (S (length al)) junk = al ++ [zb 0] -> (16 <= length junk)%nat ->
  exists v, memcmp_model junk (link_spec.S_SERVED ++ [zb 0]) 15 = Some v /\ - 256 < v < 256
            /\ (v = 0 <-> al = link_spec.S_SERVED).
Proof.
  intros al junk Na Hj Lj.
  destruct (memcmp_walk_junk link_spec.S_SERVED al junk Na S_SERVED_no_nul Hj
    ltac:(change (length link_spec.S_SERVED) with 14%nat; lia)) as (v & Hv & Rv & Iv).
  exists v. split; [exact Hv | split; [exact Rv | exact Iv]].
Qed.

(* a C string at a, read as the prefix of the bytes there *)
Lemma cstr_prefix : forall m a s big, cstr_at m a s -> bytes_at rsegs m a big ->
  (length s < length big)%nat -> firstn (S (length s)) big = s ++ [zb 0].
Proof.
  intros m a s big [B N] Bb L.
  pose proof Bb as Bb'. rewrite <- (firstn_skipn (S (length s)) big) in Bb'.
  apply bytes_at_prefix in Bb'.
  apply (bytes_at_unique m a); [exact Bb' | exact B |].
  rewrite length_firstn, length_app. cbn [length]. lia.
Qed.

(* ==========================================================================
   6. printf arguments (printf_facts_c `pf_arg_ok`)
   ========================================================================== *)

(* the int32 a register holds in its low 32 bits *)
Definition sx32 (z : Z) : Z := let w := z mod 2 ^ 32 in if w <? 2 ^ 31 then w else w - 2 ^ 32.

Lemma sx32_range : forall z, - 2 ^ 31 <= sx32 z < 2 ^ 31.
Proof.
  intros z. assert (P31 : 2 ^ 31 = 2147483648) by reflexivity. assert (P32 : 2 ^ 32 = 4294967296) by reflexivity.
  unfold sx32. cbv zeta. pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(lia)) as H.
  destruct (Z.ltb_spec (z mod 2 ^ 32) (2 ^ 31)); lia.
Qed.

Lemma int_arg_ok : forall m Sp lo D n (r : word), pf_arg_ok m Sp lo D n r (AInt (sx32 (bv_unsigned r))).
Proof.
  intros m Sp lo D n r. cbn [pf_arg_ok]. split; [apply sx32_range|].
  assert (P31 : 2 ^ 31 = 2147483648) by reflexivity. assert (P32 : 2 ^ 32 = 4294967296) by reflexivity.
  unfold sx32. cbv zeta.
  pose proof (Z.mod_pos_bound (bv_unsigned r) (2 ^ 32) ltac:(lia)) as H.
  destruct (Z.ltb_spec (bv_unsigned r mod 2 ^ 32) (2 ^ 31)).
  - rewrite (Z.mod_small (bv_unsigned r mod 2 ^ 32)) by lia. reflexivity.
  - replace (bv_unsigned r mod 2 ^ 32 - 2 ^ 32) with (bv_unsigned r mod 2 ^ 32 + (-1) * 2 ^ 32) by ring.
    rewrite Z_mod_plus_full. rewrite (Z.mod_small (bv_unsigned r mod 2 ^ 32)) by lia. reflexivity.
Qed.

Lemma byte_rt : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma pfb_map : forall s : list byte, map (Z_to_bv 8) (map bv_unsigned s) = s.
Proof. induction s as [|b s IH]; [reflexivity|]. cbn [map]. rewrite IH, byte_rt. reflexivity. Qed.

Lemma pfb_nul : forall s : list byte, pf_bytes (map bv_unsigned s ++ [0]) = s ++ [zb 0].
Proof. intros s. unfold pf_bytes. rewrite map_app, pfb_map. reflexivity. Qed.

Lemma forall_pos_of_nonul : forall s : list byte, ~ In (zb 0) s ->
  Forall (fun c => 0 < c < 256) (map bv_unsigned s).
Proof.
  intros s N. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
  pose proof (byte_range b) as R.
  assert (bv_unsigned b <> 0) by (intros E; apply N; rewrite <- (byte_zero b E); exact Hb). lia.
Qed.

(* the interface name: a C string with the slack bytes the Pre gives *)
Lemma name_arg_ok : forall m (r : word) s slack Sp lo D n,
  cstr_at m (bv_unsigned r) s -> bv_unsigned r <> 0 ->
  bytes_at rsegs m (bv_unsigned r + Z.of_nat (length s) + 1) slack ->
  Z.of_nat (length slack) = (- (bv_unsigned r + Z.of_nat (length s) + 1)) mod 8 ->
  (bv_unsigned r + Z.of_nat (length s) + 8 <= lo \/ Sp <= bv_unsigned r) ->
  (bv_unsigned r + Z.of_nat (length s) + 8 <= D \/ D + n <= bv_unsigned r) ->
  pf_arg_ok m Sp lo D n r (APtr (map bv_unsigned s)).
Proof.
  intros m r s slack Sp lo D n [B N] Hr0 Bs Ls Hlo HD.
  cbn [pf_arg_ok]. split; [apply forall_pos_of_nonul; exact N|].
  exists slack. rewrite pfb_nul, length_map.
  pose proof (Z.mod_pos_bound (- (bv_unsigned r + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hm.
  pose proof (u64_range r) as Rr.
  split; [|split; [lia|split; [lia|split; lia]]].
  apply (proj2 (bytes_at_app rsegs m (bv_unsigned r) (s ++ [zb 0]) slack)). split; [exact B|].
  replace (bv_unsigned r + Z.of_nat (length (s ++ [zb 0]))) with (bv_unsigned r + Z.of_nat (length s) + 1)
    by (rewrite length_app; cbn [length]; lia).
  exact Bs.
Qed.

(* a constant string of .rodata (link_msgs_fit `str_ok`) *)
Lemma ro_arg_ok : forall m A s slack Sp lo D n, str_ok A s slack -> mem_inv rsegs m ->
  RO_END <= lo -> (D + n <= RO_LO \/ RO_END <= D) ->
  pf_arg_ok m Sp lo D n (Z_to_bv 64 A) (APtr s).
Proof.
  intros m A s slack Sp lo D n (Hb & Hm & H1 & H2 & Hf) MI Hlo HD.
  unfold RO_LO, RO_END in *.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  cbn [pf_arg_ok]. rewrite HA. split; [exact Hf|].
  exists (pf_bytes slack).
  assert (Ll : length (pf_bytes slack) = length slack) by (unfold pf_bytes; apply length_map).
  rewrite Ll.
  split; [exact (Hb m MI)|]. split; [exact Hm|]. split; [lia|]. split; lia.
Qed.

(* the alias: a C string in front of at least 8 more readable bytes of the frame *)
Lemma alias_arg_ok : forall m (r : word) al big Sp lo D n,
  ~ In (zb 0) al -> bytes_at rsegs m (bv_unsigned r) big -> firstn (S (length al)) big = al ++ [zb 0] ->
  (length al + 8 <= length big)%nat -> 0 < bv_unsigned r ->
  (bv_unsigned r + Z.of_nat (length big) <= lo \/ Sp <= bv_unsigned r) ->
  (bv_unsigned r + Z.of_nat (length big) <= D \/ D + n <= bv_unsigned r) ->
  pf_arg_ok m Sp lo D n r (APtr (map bv_unsigned al)).
Proof.
  intros m r al big Sp lo D n Na Bb Hpre Lb Hr Hlo HD.
  cbn [pf_arg_ok]. split; [apply forall_pos_of_nonul; exact Na|].
  exists (firstn 7 (skipn (S (length al)) big)).
  rewrite pfb_nul, length_map.
  assert (L7 : length (firstn 7 (skipn (S (length al)) big)) = 7%nat)
    by (rewrite length_firstn, length_skipn; lia).
  rewrite L7.
  pose proof (Z.mod_pos_bound (- (bv_unsigned r + Z.of_nat (length al) + 1)) 8 ltac:(lia)) as Hm.
  split; [|split; [lia|split; [lia|split; lia]]].
  assert (E : big = ((al ++ [zb 0]) ++ firstn 7 (skipn (S (length al)) big))
                    ++ skipn 7 (skipn (S (length al)) big)).
  { rewrite <- app_assoc, firstn_skipn, <- Hpre. symmetry. apply firstn_skipn. }
  rewrite E in Bb. exact (bytes_at_prefix _ _ _ _ Bb).
Qed.

Lemma pf_bytes_map : forall s : list byte, pf_bytes (map bv_unsigned s) = s.
Proof. intros s. unfold pf_bytes. apply pfb_map. Qed.

Lemma text_read : forall s v, exists T, pf_text PS_READ [APtr s; AInt v] = Some T.
Proof. intros s v. eexists. reflexivity. Qed.
Lemma text_mark : forall s s2 v c, exists T, pf_text PS_MARK [APtr s; APtr s2; AInt v; APtr c] = Some T.
Proof. intros s s2 v c. eexists. reflexivity. Qed.
Lemma text_vlan : forall s, exists T, pf_text PS_VLAN [APtr s] = Some T.
Proof. intros s. eexists. reflexivity. Qed.
Lemma text_host : forall s a, exists T, pf_text PS_HOST [APtr s; APtr a] = Some T.
Proof. intros s a. eexists. reflexivity. Qed.
