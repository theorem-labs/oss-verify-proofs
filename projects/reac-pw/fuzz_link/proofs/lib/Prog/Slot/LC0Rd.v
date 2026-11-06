(* op_read (fuzz_link.c:677-700), plain image: segment S3a, from the return of text_buf (ac) at
   0x13e5c to the return of reac_link_alias_read at 0x13ed4 (LC0Defs' c0_mid).

     0x13e5c  mv   s4, a0                     s4 = the alias buffer
     0x13e60  memset (sp+0x78, 0, 40)         wk
     0x13e70  memset (sp+0x50, 0, 40)         wa
     0x13e80  lw   s9, 0x218(s1)              s9 = g_nl.opened before the two readers
     0x13e84  a2 = kc ? sp+0x78 : 0, a4 = ac ? sp+0x50 : 0, a0 = md, a1 = name, a3 = kc, a5 = ac
     0x13eb4  jal  model_read                 s7 = its answer (0x13eb8)
     0x13ebc  a0 = name, a1 = kind, a2 = kc, a3 = alias, a4 = ac
     0x13ed0  jal  reac_link_alias_read       returns to 0x13ed4: the cut

   The callee contracts enter as Section hypotheses. Every address is read from the plain image
   (link/ct/dis/plain/LLVMFuzzerTestOneInput.s). Several generic lemmas below are copies of
   lib/Prog/Slot/LC3Lib.v, renamed with the prefix rd_. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c memset_c
  model_read_c reac_link_alias_read_c mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC0Defs LC0Call LC0Lib LC0Kern.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Generic tools
   ========================================================================== *)

Lemma rd_not_outside : forall W x, ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn in H; [exfalso; exact (H I)|].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH x) as (l & h & Hin & Hx).
    + intros HO. apply H. split; [lia | exact HO].
    + exists l, h. split; [right; exact Hin | exact Hx].
  - destruct (IH x) as (l & h & Hin & Hx).
    + intros HO. apply H. split; [lia | exact HO].
    + exists l, h. split; [right; exact Hin | exact Hx].
Qed.

Lemma rd_le4_slice : forall bs off, 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  le4 (wz (fld_u32 bs off)) = firstn 4 (skipn (Z.to_nat off) bs).
Proof.
  intros bs off H0 H4. unfold fld_u32, link_spec.rdn, slice, le4, wz.
  change (Z.to_nat 4) with 4%nat.
  assert (Hl : length (firstn 4 (skipn (Z.to_nat off) bs)) = 4%nat)
    by (rewrite length_firstn, length_skipn; lia).
  rewrite unsigned_lit_wrap.
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia.
  rewrite <- Hl at 1. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

Lemma rd_u8arr_rd32 : forall m A bs off a, u8arr rsegs m A bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  a = A + off -> ov_read_bytes rsegs m (Z_to_bv 64 a) 4 = Some (le4 (wz (fld_u32 bs off))).
Proof.
  intros m A bs off a [HB _] H0 H4 ->. rewrite rd_le4_slice by lia.
  exact (bytes_at_read rsegs m A bs off 4 HB H0 ltac:(lia)).
Qed.

(* ==========================================================================
   2. The segment's footprint
   ========================================================================== *)

(* the bytes a buffer of cap c owns when its pointer is NULL for c = 0 *)
Definition rd_cap (c : Z) : Z := if c =? 0 then 0 else c.

(* what S3a writes: the stack below the frame (the callees' frames), wa and wk, the model block,
   the part of g_nl the alias reader writes, errno, and the two heap buffers *)
Definition rd_W (E : lenv) (kc K ac A : Z) : list ivl :=
  [(e_S E - SLOT_STACK_Z, e_S E - SLOT_FRAME); (e_S E - SLOT_FRAME + FO_B40, e_S E - SLOT_FRAME + FO_B256 + 40);
   (e_md E, e_md E + MD_SIZE); (A_G_NL, A_G_NL + NK_N_SENT + 4); (A_ERRNO, A_ERRNO + 4);
   (K, K + rd_cap kc); (A, A + rd_cap ac)].

(* what model_read writes, and what the alias reader writes *)
Definition rd_Wm (E : lenv) (kc ac : Z) : list ivl :=
  [(e_S E - SLOT_STACK_Z, e_S E - SLOT_FRAME); (e_md E, e_md E + MD_SIZE);
   (e_S E - SLOT_FRAME + FO_B256, e_S E - SLOT_FRAME + FO_B256 + rd_cap kc);
   (e_S E - SLOT_FRAME + FO_B40, e_S E - SLOT_FRAME + FO_B40 + rd_cap ac)].
Definition rd_Wa (E : lenv) (kc K ac A : Z) : list ivl :=
  [(e_S E - SLOT_STACK_Z, e_S E - SLOT_FRAME); (A_G_NL, A_G_NL + NK_N_SENT + 4); (A_ERRNO, A_ERRNO + 4);
   (K, K + rd_cap kc); (A, A + rd_cap ac)].

(* the placement facts the footprint lemmas use *)
Definition rd_env (E : lenv) (kc K ac A : Z) : Prop :=
  lenv_ok E /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\ (kc = 0 -> K = 0) /\ (ac = 0 -> A = 0) /\
  (kc <> 0 -> c0_blk E K (kc + 1)) /\ (ac <> 0 -> c0_blk E A (ac + 1)) /\
  (kc <> 0 -> ac <> 0 -> apart K (kc + 1) A (ac + 1)).

(* a heap buffer, as the footprint sees it *)
Lemma rd_buf_facts : forall E c B, lenv_ok E -> 0 <= c < 40 -> (c = 0 -> B = 0) -> (c <> 0 -> c0_blk E B (c + 1)) ->
  (c = 0 /\ B = 0 /\ rd_cap c = 0) \/
  (c <> 0 /\ rd_cap c = c /\ 4096 <= B /\ B + c + 1 <= e_S E - SLOT_STACK_Z /\
   (B + c + 1 <= 0x10000 \/ 0x97000 <= B) /\ apart B (c + 1) (e_md E) MD_SIZE /\
   apart B (c + 1) (e_mk E) MK_SIZE /\ apart B (c + 1) (e_p0 E) (Z.of_nat (length (e_pl E)))).
Proof.
  intros E c B HE Hc H0 Hb. unfold rd_cap. destruct (Z.eqb_spec c 0) as [E0|E0].
  - left. split; [exact E0|]. split; [exact (H0 E0) | reflexivity].
  - right. destruct (Hb E0) as ((H1 & H2 & H3) & H4 & H5 & H6).
    split; [exact E0|]. split; [reflexivity|]. split; [exact H1|]. split; [lia|].
    split; [pose proof (c0_img_free _ _ H3 ltac:(lia)); lia|]. split; [exact H4|]. split; [exact H5 | exact H6].
Qed.

(* the facts of lenv_ok the footprint lemmas use, with the constants unfolded *)
Lemma rd_lenv_facts : forall E, lenv_ok E ->
  0x960e0 + 65536 <= e_S E <= 2 ^ 47 /\
  4096 <= e_md E /\ e_md E + 8856 <= e_S E - 65536 /\ (e_md E + 8856 <= 0x10000 \/ 0x97000 <= e_md E) /\
  4096 <= e_mk E /\ e_mk E + 516 <= e_S E - 65536 /\ (e_mk E + 516 <= 0x10000 \/ 0x97000 <= e_mk E) /\
  (e_md E + 8856 <= e_mk E \/ e_mk E + 516 <= e_md E) /\
  1 <= Z.of_nat (length (e_pl E)) /\ 4096 <= e_p0 E /\ e_p0 E + Z.of_nat (length (e_pl E)) <= e_S E - 65536 /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= 0x10000 \/ 0x97000 <= e_p0 E) /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_md E \/ e_md E + 8856 <= e_p0 E) /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_mk E \/ e_mk E + 516 <= e_p0 E).
Proof.
  intros E (HS1 & HS2 & _ & (M1 & M2 & M3) & (K1 & K2 & K3) & _ & _ & HMK & (L1 & _) & (P1 & P2 & P3) & HPM & HPK & _).
  unfold SLOT_STACK_Z, MD_SIZE, MK_SIZE in *.
  pose proof (c0_img_free _ _ M3 ltac:(lia)). pose proof (c0_img_free _ _ K3 ltac:(lia)).
  pose proof (c0_img_free _ _ P3 ltac:(lia)).
  repeat split; try lia.
Qed.

Ltac rd_consts :=
  unfold SLOT_STACK_Z, SLOT_FRAME, FO_B40, FO_B256, MD_SIZE, MK_SIZE, A_ERRNO, A_TP, ERRNO_TP_OFF,
    A_G_NL, NK_N_SENT, NK_SIZE, apart in *.

(* a range inside the image, apart from the two pieces of it the segment writes *)
Lemma rd_disj_img : forall E kc K ac A a n, rd_env E kc K ac A -> 0 <= n ->
  0x10000 <= a -> a + n <= 0x960e0 ->
  (a + n <= A_G_NL \/ A_G_NL + NK_N_SENT + 4 <= a) -> (a + n <= A_ERRNO \/ A_ERRNO + 4 <= a) ->
  disjoint_from (rd_W E kc K ac A) a n.
Proof.
  intros E kc K ac A a n (HE & Hkc & Hac & HK0 & HA0 & HKb & HAb & _) Hn H1 H2 Hg He.
  pose proof (rd_buf_facts E kc K HE Hkc HK0 HKb) as HK.
  pose proof (rd_buf_facts E ac A HE Hac HA0 HAb) as HA.
  pose proof (rd_lenv_facts E HE) as (HS & Hm1 & Hm2 & Hm3 & _).
  clear - HS Hm1 Hm2 Hm3 HK HA Hn H1 H2 Hg He.
  cbn [disjoint_from rd_W]. rd_consts.
  repeat split; lia.
Qed.

(* a heap range below the stack, outside the image, apart from md and the two buffers *)
Lemma rd_disj_heap : forall E kc K ac A a n, rd_env E kc K ac A -> 0 <= n -> 0 <= a ->
  a + n <= e_S E - SLOT_STACK_Z -> (a + n <= 0x10000 \/ 0x97000 <= a) ->
  apart a n (e_md E) MD_SIZE -> (kc <> 0 -> apart a n K (kc + 1)) -> (ac <> 0 -> apart a n A (ac + 1)) ->
  disjoint_from (rd_W E kc K ac A) a n.
Proof.
  intros E kc K ac A a n (HE & Hkc & Hac & HK0 & HA0 & HKb & HAb & _) Hn Ha H1 H2 Hm HaK HaA.
  pose proof (rd_buf_facts E kc K HE Hkc HK0 HKb) as HK.
  pose proof (rd_buf_facts E ac A HE Hac HA0 HAb) as HA.
  pose proof (rd_lenv_facts E HE) as (HS & _).
  assert (HK' : (K = 0 /\ rd_cap kc = 0) \/ (rd_cap kc = kc /\ apart a n K (kc + 1))).
  { destruct HK as [(E0 & E1 & E2) | (E0 & E1 & _)]; [left; split; assumption | right; split; [exact E1 | exact (HaK E0)]]. }
  assert (HA' : (A = 0 /\ rd_cap ac = 0) \/ (rd_cap ac = ac /\ apart a n A (ac + 1))).
  { destruct HA as [(E0 & E1 & E2) | (E0 & E1 & _)]; [left; split; assumption | right; split; [exact E1 | exact (HaA E0)]]. }
  clear - HS HK' HA' Hn Ha H1 H2 Hm Hkc Hac.
  cbn [disjoint_from rd_W]. rd_consts.
  repeat split; lia.
Qed.

(* a range of the frame outside wa and wk: the cells below 0x50 and above 0xa0, and the saved bytes *)
Lemma rd_disj_frame : forall E kc K ac A a n, rd_env E kc K ac A -> 0 <= n ->
  ((e_S E - SLOT_FRAME <= a /\ a + n <= e_S E - SLOT_FRAME + FO_B40) \/
   (e_S E - SLOT_FRAME + FO_B256 + 40 <= a /\ a + n <= e_S E)) ->
  disjoint_from (rd_W E kc K ac A) a n.
Proof.
  intros E kc K ac A a n (HE & Hkc & Hac & HK0 & HA0 & HKb & HAb & _) Hn Ha.
  pose proof (rd_buf_facts E kc K HE Hkc HK0 HKb) as HK.
  pose proof (rd_buf_facts E ac A HE Hac HA0 HAb) as HA.
  pose proof (rd_lenv_facts E HE) as (HS & Hm1 & Hm2 & _).
  clear - HS Hm1 Hm2 HK HA Hn Ha.
  cbn [disjoint_from rd_W]. rd_consts.
  repeat split; lia.
Qed.

(* the guard byte after a heap buffer *)
Lemma rd_disj_kguard : forall E kc K ac A, rd_env E kc K ac A -> kc <> 0 ->
  disjoint_from (rd_W E kc K ac A) (K + kc) 1.
Proof.
  intros E kc K ac A (HE & Hkc & Hac & HK0 & HA0 & HKb & HAb & HKA) Hk.
  pose proof (rd_buf_facts E kc K HE Hkc HK0 HKb) as HK.
  pose proof (rd_buf_facts E ac A HE Hac HA0 HAb) as HA.
  pose proof (rd_lenv_facts E HE) as (HS & _).
  assert (HA' : (A = 0 /\ rd_cap ac = 0) \/ (rd_cap ac = ac /\ apart K (kc + 1) A (ac + 1))).
  { destruct HA as [(E0 & E1 & E2) | (E0 & E1 & _)]; [left; split; assumption | right; split; [exact E1 | exact (HKA Hk E0)]]. }
  destruct HK as [(E0 & _) | (_ & HK1 & HK2 & HK3 & HK4 & HK5 & _)]; [exfalso; exact (Hk E0)|].
  clear - HS HA' HK1 HK2 HK3 HK4 HK5 Hkc Hac.
  cbn [disjoint_from rd_W]. rd_consts.
  repeat split; lia.
Qed.

Lemma rd_disj_aguard : forall E kc K ac A, rd_env E kc K ac A -> ac <> 0 ->
  disjoint_from (rd_W E kc K ac A) (A + ac) 1.
Proof.
  intros E kc K ac A (HE & Hkc & Hac & HK0 & HA0 & HKb & HAb & HKA) Ha.
  pose proof (rd_buf_facts E kc K HE Hkc HK0 HKb) as HK.
  pose proof (rd_buf_facts E ac A HE Hac HA0 HAb) as HA.
  pose proof (rd_lenv_facts E HE) as (HS & _).
  assert (HK' : (K = 0 /\ rd_cap kc = 0) \/ (rd_cap kc = kc /\ apart K (kc + 1) A (ac + 1))).
  { destruct HK as [(E0 & E1 & E2) | (E0 & E1 & _)]; [left; split; assumption | right; split; [exact E1 | exact (HKA E0 Ha)]]. }
  destruct HA as [(E0 & _) | (_ & HA1 & HA2 & HA3 & HA4 & HA5 & _)]; [exfalso; exact (Ha E0)|].
  clear - HS HK' HA1 HA2 HA3 HA4 HA5 Hkc Hac.
  cbn [disjoint_from rd_W]. rd_consts.
  repeat split; lia.
Qed.

(* the four writes of the segment lie inside its footprint *)
Lemma rd_sub_wk : forall E kc K ac A,
  sub_fp [(e_S E - SLOT_FRAME + FO_B256, e_S E - SLOT_FRAME + FO_B256 + 40)] (rd_W E kc K ac A).
Proof.
  intros E kc K ac A x Hx. cbn [outside rd_W] in *. destruct Hx as (_ & X & _).
  split; [|exact I]. intros C. apply X. rd_consts. lia.
Qed.

Lemma rd_sub_wa : forall E kc K ac A,
  sub_fp [(e_S E - SLOT_FRAME + FO_B40, e_S E - SLOT_FRAME + FO_B40 + 40)] (rd_W E kc K ac A).
Proof.
  intros E kc K ac A x Hx. cbn [outside rd_W] in *. destruct Hx as (_ & X & _).
  split; [|exact I]. intros C. apply X. rd_consts. lia.
Qed.

Lemma rd_sub_m : forall E kc K ac A, 0 <= kc < 40 -> 0 <= ac < 40 -> sub_fp (rd_Wm E kc ac) (rd_W E kc K ac A).
Proof.
  intros E kc K ac A Hk Ha x Hx. cbn [outside rd_W rd_Wm] in *.
  assert (0 <= rd_cap kc <= kc /\ 0 <= rd_cap ac <= ac) by (unfold rd_cap; destruct (kc =? 0), (ac =? 0); lia).
  rd_consts. destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _). repeat split; lia.
Qed.

Lemma rd_sub_a : forall E kc K ac A, sub_fp (rd_Wa E kc K ac A) (rd_W E kc K ac A).
Proof.
  intros E kc K ac A x Hx. cbn [outside rd_W rd_Wa] in *.
  destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _). repeat split; assumption.
Qed.

(* ==========================================================================
   3. The loop's memory facts across the segment's writes
   ========================================================================== *)

Section Keep.
Variables (E : lenv) (kc K ac A : Z) (m m' : word -> option byte).
Hypothesis HENV : rd_env E kc K ac A.
Hypothesis MU : munch (rd_W E kc K ac A) m m'.
Hypothesis WM : wmono rsegs m m'.

Lemma rd_keep_img : forall a bs, 0x10000 <= a -> a + Z.of_nat (length bs) <= 0x960e0 ->
  (a + Z.of_nat (length bs) <= A_G_NL \/ A_G_NL + NK_N_SENT + 4 <= a) ->
  (a + Z.of_nat (length bs) <= A_ERRNO \/ A_ERRNO + 4 <= a) ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros a bs H1 H2 H3 H4 HB. eapply (bytes_at_transport rsegs); [exact HB | exact MU|].
  apply rd_disj_img; auto. lia.
Qed.

(* below g_nl: .rodata and .data.rel.ro *)
Lemma rd_keep_lo : forall a bs, 0x10000 <= a -> a + Z.of_nat (length bs) <= A_G_NL ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros a bs H1 H2 HB. apply rd_keep_img; auto; unfold A_G_NL, A_ERRNO, A_TP, ERRNO_TP_OFF in *; lia.
Qed.

Lemma rd_keep_cstr_lo : forall a s, 0x10000 <= a -> a + Z.of_nat (length s) + 1 <= A_G_NL ->
  cstr_at m a s -> cstr_at m' a s.
Proof.
  intros a s H1 H2 [HB HN]. split; [|exact HN].
  apply rd_keep_lo; [exact H1 | rewrite length_app; cbn [length]; lia | exact HB].
Qed.

Lemma rd_keep_u64_lo : forall a v, 0x10000 <= a -> a + 8 <= A_G_NL -> u64_at m a v -> u64_at m' a v.
Proof. intros a v H1 H2 HB. apply rd_keep_lo; [exact H1 | rewrite length_le8; lia | exact HB]. Qed.

Lemma rd_odd_bounds : forall i, (i < 6)%nat ->
  0x10000 <= nth i odd_ptrs 0 /\ nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= 0x11000.
Proof. intros i Hi. do 6 (destruct i as [|i]; [cbn; lia|]). lia. Qed.

Lemma rd_keep_gnames : gnames_at m -> gnames_at m'.
Proof.
  intros H k Hk. destruct (H k Hk) as (rest & HB & HL). exists rest. split; [|exact HL].
  apply rd_keep_img; [unfold A_G_NAMES; lia | rewrite HL; unfold A_G_NAMES; lia
    | rewrite HL; right; unfold A_G_NAMES, A_G_NL, NK_N_SENT; lia
    | rewrite HL; left; unfold A_G_NAMES, A_ERRNO, A_TP, ERRNO_TP_OFF; lia | exact HB].
Qed.

Lemma rd_keep_odd : odd_at m -> odd_at m'.
Proof.
  intros H i Hi. destruct (H i Hi) as [HU HC]. pose proof (rd_odd_bounds i Hi) as (B1 & B2). split.
  - apply rd_keep_u64_lo; [unfold A_ODD; lia | unfold A_ODD, A_G_NL; lia | exact HU].
  - apply rd_keep_cstr_lo; [exact B1 | unfold A_G_NL; lia | exact HC].
Qed.

Lemma rd_keep_policy : policy_ro m -> policy_ro m'.
Proof.
  intros (H1 & H2 & H3 & H4).
  split; [|split; [|split]]; (apply rd_keep_cstr_lo; [ | | eassumption]);
    unfold A_PREFIX, A_SERVED, A_VLAN, A_EMPTY, A_G_NL; cbn; lia.
Qed.

Lemma rd_keep_la : la_ok m -> la_ok m'.
Proof.
  intros (la & sl & HC & HB & HL). exists la, sl. split; [|split; [|exact HL]].
  - eapply (rw_cells_transport rsegs); [exact HC | exact MU | exact WM|].
    apply rd_disj_img; auto; cbn [cells_size csize]; unfold A_LONG_ALIAS, A_G_NL, NK_N_SENT, A_ERRNO, A_TP, ERRNO_TP_OFF; lia.
  - apply rd_keep_img; [ | | | | exact HB]; rewrite ?HL;
      unfold A_LONG_ALIAS, LONG_ALIAS_SIZE, A_G_NL, NK_N_SENT, A_ERRNO, A_TP, ERRNO_TP_OFF; lia.
Qed.

Lemma rd_keep_texts : texts_at m -> texts_at m'.
Proof.
  intros H i Hi. apply rd_keep_u64_lo; [unfold A_TEXTS; lia | unfold A_TEXTS, A_G_NL; lia | exact (H i Hi)].
Qed.

Lemma rd_keep_ifptrs : ifptrs_at m -> ifptrs_at m'.
Proof.
  intros H i Hi. apply rd_keep_img; [ | | | | exact (H i Hi)]; rewrite ?length_le8;
    unfold A_G_NL, NK_IF_NAME, NK_N_SENT, A_ERRNO, A_TP, ERRNO_TP_OFF; lia.
Qed.

Lemma rd_keep_guard : guard_m m -> guard_m m'.
Proof.
  intros (H1 & c & H2). split; [|exists c].
  - apply rd_keep_lo; [ | | exact H1]; rewrite ?length_le8; unfold A_GOT_GUARD_S, A_G_NL; lia.
  - apply rd_keep_img; [ | | | | exact H2]; rewrite ?length_le8;
      unfold A_GUARD_S, A_G_NL, NK_N_SENT, A_ERRNO, A_TP, ERRNO_TP_OFF; lia.
Qed.

Lemma rd_keep_frame_bytes : forall a bs,
  ((e_S E - SLOT_FRAME <= a /\ a + Z.of_nat (length bs) <= e_S E - SLOT_FRAME + FO_B40) \/
   (e_S E - SLOT_FRAME + FO_B256 + 40 <= a /\ a + Z.of_nat (length bs) <= e_S E)) ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros a bs Ha HB. eapply (bytes_at_transport rsegs); [exact HB | exact MU|].
  apply rd_disj_frame; [exact HENV | lia | exact Ha].
Qed.

Lemma rd_keep_frame_cells : forall a cs,
  ((e_S E - SLOT_FRAME <= a /\ a + Z.of_nat (cells_size cs) <= e_S E - SLOT_FRAME + FO_B40) \/
   (e_S E - SLOT_FRAME + FO_B256 + 40 <= a /\ a + Z.of_nat (cells_size cs) <= e_S E)) ->
  rw_cells rsegs m a cs -> rw_cells rsegs m' a cs.
Proof.
  intros a cs Ha HC. eapply (rw_cells_transport rsegs); [exact HC | exact MU | exact WM|].
  apply rd_disj_frame; [exact HENV | lia | exact Ha].
Qed.

Lemma rd_keep_marks : forall gbs, marks_at m (e_mk E) gbs -> marks_at m' (e_mk E) gbs.
Proof.
  intros gbs [HU HL]. split; [|exact HL].
  destruct HENV as (HE & Hkc & Hac & _ & _ & HKb & HAb & _).
  pose proof (rd_lenv_facts E HE) as (_ & _ & _ & _ & K1 & K2 & K3 & HMK & _).
  eapply (u8arr_transport rsegs); [exact HU | exact MU | exact WM|].
  rewrite HL. apply rd_disj_heap; [exact HENV | unfold MK_SIZE; lia | lia | unfold MK_SIZE, SLOT_STACK_Z; lia
    | unfold MK_SIZE; lia | unfold apart, MK_SIZE, MD_SIZE; lia | | ].
  - intros Hk. destruct (HKb Hk) as (_ & _ & H & _). unfold apart in *. lia.
  - intros Ha. destruct (HAb Ha) as (_ & _ & H & _). unfold apart in *. lia.
Qed.

Lemma rd_keep_cursor : forall P N, cursor_ok m (e_p0 E) (e_pl E) P N -> cursor_ok m' (e_p0 E) (e_pl E) P N.
Proof.
  intros P N [HB HK]. split; [|exact HK].
  destruct HENV as (HE & Hkc & Hac & _ & _ & HKb & HAb & _).
  pose proof (rd_lenv_facts E HE) as (_ & _ & _ & _ & _ & _ & _ & _ & L1 & P1 & P2 & P3 & HPM & _).
  eapply (bytes_at_transport rsegs); [exact HB | exact MU|].
  apply rd_disj_heap; [exact HENV | lia | lia | unfold SLOT_STACK_Z; lia | lia | unfold apart, MD_SIZE; lia | | ].
  - intros Hk. destruct (HKb Hk) as (_ & _ & _ & H). unfold apart in *. lia.
  - intros Ha. destruct (HAb Ha) as (_ & _ & _ & H). unfold apart in *. lia.
Qed.

Lemma rd_keep_task : MemNorm.task_mem rsegs m -> MemNorm.task_mem rsegs m'.
Proof.
  intros HT. apply (c0_task_mem_munch _ m m' HT MU). intros x Hx HO.
  destruct (rd_not_outside _ _ HO) as (lo & hi & Hin & Hr).
  destruct HENV as (HE & Hkc & Hac & HK0 & HA0 & HKb & HAb & _).
  pose proof (rd_buf_facts E kc K HE Hkc HK0 HKb) as HK.
  pose proof (rd_buf_facts E ac A HE Hac HA0 HAb) as HA.
  pose proof (rd_lenv_facts E HE) as (HS & Hm1 & Hm2 & _).
  unfold rd_W in Hin. cbn [In] in Hin. change TASK_SIZE with (2 ^ 47).
  destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; inversion E1; subst lo hi; clear E1;
    rd_consts; lia.
Qed.

End Keep.

(* the loop-head facts after the segment's writes: the kernel and the model are the new ones the
   two readers left *)
Lemma rd_base_keep : forall E P N kbs mbs gbs kbs' mbs' kc K ac A m m',
  rd_env E kc K ac A -> c0_base E P N kbs mbs gbs m ->
  munch (rd_W E kc K ac A) m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  nlk_at m' kbs' -> nlk_wf kbs' -> iftab_at m' kbs' link_tab -> nk_open kbs' = 0 -> nk_misuse kbs' = 0 ->
  model_at m' (e_md E) mbs' -> model_wf mbs' -> marks_are gbs mbs' ->
  c0_base E P N kbs' mbs' gbs m'.
Proof.
  intros E P N kbs mbs gbs kbs' mbs' kc K ac A m m' HENV HB MU WM MI ST NL NW IT NO NM MA MW KR.
  destruct HB as (SV & _ & _ & _ & _ & _ & GN & OD & PR & LA & TX & IP & _ & _ & KA & KW & _ & CU & ER & GU & _ & TM & _).
  pose proof (proj1 HENV) as HE.
  unfold c0_base.
  split; [apply (rd_keep_frame_bytes E kc K ac A m m' HENV MU); [|exact SV]|].
  { right. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL). rewrite HL.
    unfold SLOT_FRAME, FO_B256. lia. }
  split; [exact NL|]. split; [exact NW|]. split; [exact IT|]. split; [exact NO|]. split; [exact NM|].
  split; [exact (rd_keep_gnames E kc K ac A m m' HENV MU GN)|].
  split; [exact (rd_keep_odd E kc K ac A m m' HENV MU OD)|].
  split; [exact (rd_keep_policy E kc K ac A m m' HENV MU PR)|].
  split; [exact (rd_keep_la E kc K ac A m m' HENV MU WM LA)|].
  split; [exact (rd_keep_texts E kc K ac A m m' HENV MU TX)|].
  split; [exact (rd_keep_ifptrs E kc K ac A m m' HENV MU IP)|].
  split; [exact MA|]. split; [exact MW|].
  split; [exact (rd_keep_marks E kc K ac A m m' HENV MU WM gbs KA)|].
  split; [exact KW|]. split; [exact KR|].
  split; [exact (rd_keep_cursor E kc K ac A m m' HENV MU P N CU)|].
  split; [exact (wr_at_transport rsegs m m' _ _ ER WM)|].
  split; [exact (rd_keep_guard E kc K ac A m m' HENV MU GU)|].
  split; [exact MI|]. split; [exact (rd_keep_task E kc K ac A m m' HENV MU TM)|]. exact ST.
Qed.

Lemma rd_getr10 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word,
  getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 10 = a0.
Proof. reflexivity. Qed.
(* ==========================================================================
   4. The frame and the text buffers
   ========================================================================== *)

Definition rd_pre (md mk P N : Z) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); C8 (wz (md + MD_MARK)); C8 (wz A_EMPTY); C8 (wz mk); C8 (wz A_G_NAMES);
   C8 (wz A_JT); C8 (wz GNL42); C8 (wz P); C8 (wz N)].

Lemma rd_frame_split : forall E P N wa wk m, c0_frame E P N wa wk m ->
  exists j0 j2, rw_cells rsegs m (e_S E - SLOT_FRAME) (rd_pre (e_md E) (e_mk E) P N j0) /\
    rw_cells rsegs m (e_S E - SLOT_FRAME + FO_B40) [CB 40 wa] /\
    rw_cells rsegs m (e_S E - SLOT_FRAME + FO_B256) [CB 40 wk] /\
    rw_cells rsegs m (e_S E - SLOT_FRAME + FO_B256 + 40) [CB 216 j2].
Proof.
  intros E P N wa wk m (j0 & j2 & H). exists j0, j2.
  change (c0_cells (e_md E) (e_mk E) P N j0 wa wk j2) with
    (rd_pre (e_md E) (e_mk E) P N j0 ++ [CB 40 wa] ++ [CB 40 wk] ++ [CB 216 j2]) in H.
  apply c0_rw_app in H as [H1 H]. apply c0_rw_app in H as [H2 H].
  apply c0_rw_app in H as [H3 H4].
  change (Z.of_nat (cells_size (rd_pre (e_md E) (e_mk E) P N j0))) with 80 in H2, H3, H4.
  change (Z.of_nat (cells_size [CB 40 wa])) with 40 in H3, H4.
  change (Z.of_nat (cells_size [CB 40 wk])) with 40 in H4.
  unfold FO_B40, FO_B256.
  replace (e_S E - SLOT_FRAME + 120) with (e_S E - SLOT_FRAME + 80 + 40) by lia.
  replace (e_S E - SLOT_FRAME + 80 + 40 + 40) with (e_S E - SLOT_FRAME + 80 + 40 + 40) by lia.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Lemma rd_frame_join : forall E P N j0 wa wk j2 m,
  rw_cells rsegs m (e_S E - SLOT_FRAME) (rd_pre (e_md E) (e_mk E) P N j0) ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_B40) [CB 40 wa] ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_B256) [CB 40 wk] ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_B256 + 40) [CB 216 j2] ->
  c0_frame E P N wa wk m.
Proof.
  intros E P N j0 wa wk j2 m H1 H2 H3 H4. exists j0, j2.
  change (c0_cells (e_md E) (e_mk E) P N j0 wa wk j2) with
    (rd_pre (e_md E) (e_mk E) P N j0 ++ [CB 40 wa] ++ [CB 40 wk] ++ [CB 216 j2]).
  unfold FO_B40, FO_B256 in *.
  apply c0_rw_join; [exact H1|].
  change (Z.of_nat (cells_size (rd_pre (e_md E) (e_mk E) P N j0))) with 80.
  apply c0_rw_join; [exact H2|].
  change (Z.of_nat (cells_size [CB 40 wa])) with 40.
  apply c0_rw_join.
  - replace (e_S E - SLOT_FRAME + 80 + 40) with (e_S E - SLOT_FRAME + 120) by lia. exact H3.
  - change (Z.of_nat (cells_size [CB 40 wk])) with 40.
    replace (e_S E - SLOT_FRAME + 80 + 40 + 40) with (e_S E - SLOT_FRAME + 120 + 40) by lia. exact H4.
Qed.

(* the empty C string at the start of a buffer whose first byte is 0 *)
Lemma rd_cstr_nil : forall m a n bs, rw_cells rsegs m a [CB n bs] -> nth_error bs 0 = Some (zb 0) -> cstr_at m a [].
Proof.
  intros m a n bs [[[Hw _] (Ha & Hl & HB)] _] H0. cbn [cells_bytes cbytes] in Hl, HB. rewrite app_nil_r in Hl, HB.
  split; [|intros []].
  assert (L : (0 < length bs)%nat) by (destruct bs; [discriminate H0 | cbn; lia]).
  split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace i with 0%nat by lia.
  rewrite (HB 0%nat L). exact H0.
Qed.

(* a reader's buffer: the cap bytes, then the guard byte *)
Lemma rd_tbuf : forall m a cap bs, 0 <= cap -> rw_cells rsegs m a [CB (Z.to_nat cap) bs] ->
  rw_cells rsegs m (a + cap) [C1 (zb GUARD_BYTE)] -> tbuf_at m a cap bs.
Proof.
  intros m a cap bs Hc H1 H2. unfold tbuf_at.
  change [CB (Z.to_nat cap) bs; C1 (zb GUARD_BYTE)] with ([CB (Z.to_nat cap) bs] ++ [C1 (zb GUARD_BYTE)]).
  apply c0_rw_join; [exact H1|].
  change (cells_size [CB (Z.to_nat cap) bs]) with (Z.to_nat cap + 0)%nat. rewrite Nat.add_0_r, Z2Nat.id by exact Hc.
  exact H2.
Qed.

Lemma rd_guard_of : forall m a cap bs, 0 <= cap -> tbuf_at m a cap bs ->
  rw_cells rsegs m (a + cap) [C1 (zb GUARD_BYTE)].
Proof.
  intros m a cap bs Hc H. unfold tbuf_at in H.
  change [CB (Z.to_nat cap) bs; C1 (zb GUARD_BYTE)] with ([CB (Z.to_nat cap) bs] ++ [C1 (zb GUARD_BYTE)]) in H.
  apply c0_rw_app in H. destruct H as [_ H].
  change (cells_size [CB (Z.to_nat cap) bs]) with (Z.to_nat cap + 0)%nat in H.
  rewrite Nat.add_0_r, Z2Nat.id in H by exact Hc. exact H.
Qed.

(* ==========================================================================
   5. The two readers' answers
   ========================================================================== *)

Lemma rd_md_reqs0 : forall mbs, md_n_req mbs = 0 -> md_reqs mbs = [].
Proof. intros mbs H. unfold md_reqs. rewrite H. reflexivity. Qed.

Lemma rd_nk_sent0 : forall kbs, nk_n_sent kbs = 0 -> nk_sent kbs = [].
Proof. intros kbs H. unfold nk_sent. rewrite H. reflexivity. Qed.

Lemma rd_kstate : forall kbs mbs, c0_begun kbs mbs -> md_kstate mbs kbs = nk_kstate kbs.
Proof.
  intros kbs mbs (H1 & _ & H3 & _ & H5 & H6 & _). unfold md_kstate, nk_kstate.
  rewrite H1, H3, H5, H6. reflexivity.
Qed.

(* ==========================================================================
   6. Small facts the walk uses
   ========================================================================== *)

Lemma rd_q_ext : forall X, q_ext (eqv_cl X).
Proof. intros X c a (d & Hd & E1) E2. exists d. split; [exact Hd | exact (c0_ms_eqv_trans _ _ _ E1 E2)]. Qed.

(* seqz; addi -1; and: the buffer pointer, or NULL for a zero cap *)
Lemma rd_mask : forall k X, 0 <= k < 2 ^ 64 -> 0 <= X < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 k) 1) + -1)))
                     (bv_unsigned (Z_to_bv 64 X))) = Z_to_bv 64 (if k =? 0 then 0 else X).
Proof.
  intros k X Hk HX. unfold v_sltiu. rewrite (unsigned_lit k) by lia. change (bv_wrap 64 1) with 1.
  rewrite (unsigned_lit X) by lia.
  destruct (Z.eqb_spec k 0) as [->|Hn].
  - change (0 <? 1) with true. cbv iota. rewrite (unsigned_lit 1) by lia. change (1 + -1) with 0.
    rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l. reflexivity.
  - replace (k <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    rewrite (unsigned_lit 0) by lia. change (0 + -1) with (-1). rewrite unsigned_lit_wrap.
    change (-1 mod 2 ^ 64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small by lia. reflexivity.
Qed.

(* lw of a 31-bit value *)
Lemma rd_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
  change (2 ^ 32 / 2) with (2 ^ 31). rewrite Z.mod_small by lia. lia.
Qed.

Lemma rd_sel_ptr_rng : forall sel, 0 <= sel < 256 -> 0 <= sel_ptr sel < 2 ^ 64.
Proof.
  intros sel Hs. unfold sel_ptr. destruct (Z.eqb_spec sel 255); [lia|].
  destruct (Z.ltb_spec sel 64); [unfold A_G_NAMES; lia|].
  assert (Hj : (Z.to_nat (sel mod 6) < 6)%nat) by (pose proof (Z.mod_pos_bound sel 6); lia).
  destruct (c0_odd_ok _ Hj) as ((Hn & [Hr|Hr]) & _); c0_unf; lia.
Qed.

(* the write sets of the two reader calls, as the contracts state them *)
Lemma rd_sub_mcall : forall E kc ac k2 k4, lenv_ok E -> 0 <= kc < 40 -> 0 <= ac < 40 ->
  (kc = 0 -> k2 = 0) -> (kc <> 0 -> k2 = e_S E - SLOT_FRAME + FO_B256) ->
  (ac = 0 -> k4 = 0) -> (ac <> 0 -> k4 = e_S E - SLOT_FRAME + FO_B40) ->
  sub_fp [(e_S E - SLOT_FRAME - 240, e_S E - SLOT_FRAME); (e_md E, e_md E + MD_SIZE);
          (k2, k2 + (if k2 =? 0 then 0 else kc)); (k4, k4 + (if k4 =? 0 then 0 else ac))] (rd_Wm E kc ac).
Proof.
  intros E kc ac k2 k4 HE Hkc Hac K0 K1 A0 A1 x Hx. pose proof (rd_lenv_facts E HE) as (LS & _).
  cbn [outside rd_Wm] in Hx |- *. destruct Hx as (X1 & X2 & X3 & X4 & _).
  assert (H2 : (k2 = 0 /\ rd_cap kc = 0) \/ (k2 = e_S E - SLOT_FRAME + FO_B256 /\ rd_cap kc = kc /\ (k2 =? 0) = false)).
  { unfold rd_cap. destruct (Z.eqb_spec kc 0) as [E0|E0]; [left; split; [exact (K0 E0) | reflexivity]|right].
    rewrite (K1 E0). split; [reflexivity|]. split; [reflexivity|]. apply Z.eqb_neq. c0_unf; lia. }
  assert (H4 : (k4 = 0 /\ rd_cap ac = 0) \/ (k4 = e_S E - SLOT_FRAME + FO_B40 /\ rd_cap ac = ac /\ (k4 =? 0) = false)).
  { unfold rd_cap. destruct (Z.eqb_spec ac 0) as [E0|E0]; [left; split; [exact (A0 E0) | reflexivity]|right].
    rewrite (A1 E0). split; [reflexivity|]. split; [reflexivity|]. apply Z.eqb_neq. c0_unf; lia. }
  destruct H2 as [(Q1 & Q2) | (Q1 & Q2 & E2)]; destruct H4 as [(Q3 & Q4) | (Q3 & Q4 & E4)]; subst k2 k4;
    rewrite ?Q2, ?Q4, ?E2, ?E4 in *; cbn [Z.eqb] in *; c0_unf; repeat split; lia.
Qed.

Lemma rd_sub_acall : forall E kc K ac A, rd_env E kc K ac A ->
  sub_fp [(e_S E - SLOT_FRAME - 16672, e_S E - SLOT_FRAME); (A_G_NL, A_G_NL + NK_N_SENT + 4);
          (A_TP + ERRNO_TP_OFF, A_TP + ERRNO_TP_OFF + 4); (K, K + (if K =? 0 then 0 else kc));
          (A, A + (if A =? 0 then 0 else ac))] (rd_Wa E kc K ac A).
Proof.
  intros E kc K ac A (HE & Hkc & Hac & HK0 & HA0 & HKb & HAb & _) x Hx.
  pose proof (rd_buf_facts E kc K HE Hkc HK0 HKb) as HK.
  pose proof (rd_buf_facts E ac A HE Hac HA0 HAb) as HA.
  pose proof (rd_lenv_facts E HE) as (LS & _).
  cbn [outside rd_Wa] in Hx |- *. destruct Hx as (X1 & X2 & X3 & X4 & X5 & _).
  assert (EK : (if K =? 0 then 0 else kc) = rd_cap kc).
  { destruct HK as [(-> & -> & ->) | (E0 & -> & H1 & _)]; [reflexivity|].
    replace (K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (EA : (if A =? 0 then 0 else ac) = rd_cap ac).
  { destruct HA as [(-> & -> & ->) | (E0 & -> & H1 & _)]; [reflexivity|].
    replace (A =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  rewrite EK, EA. unfold A_ERRNO. c0_unf. repeat split; lia.
Qed.

(* the frame against the alias reader's writes, md against them, g_nl against model_read's *)
Lemma rd_disj_frame_a : forall E kc K ac A a n, rd_env E kc K ac A -> 0 <= n ->
  e_S E - SLOT_FRAME <= a -> a + n <= e_S E -> disjoint_from (rd_Wa E kc K ac A) a n.
Proof.
  intros E kc K ac A a n (HE & Hkc & Hac & HK0 & HA0 & HKb & HAb & _) Hn H1 H2.
  pose proof (rd_buf_facts E kc K HE Hkc HK0 HKb) as HK.
  pose proof (rd_buf_facts E ac A HE Hac HA0 HAb) as HA.
  pose proof (rd_lenv_facts E HE) as (HS & _).
  clear - HS HK HA Hn H1 H2. cbn [disjoint_from rd_Wa]. rd_consts. repeat split; lia.
Qed.

Lemma rd_disj_md_a : forall E kc K ac A, rd_env E kc K ac A -> disjoint_from (rd_Wa E kc K ac A) (e_md E) MD_SIZE.
Proof.
  intros E kc K ac A (HE & Hkc & Hac & HK0 & HA0 & HKb & HAb & _).
  pose proof (rd_buf_facts E kc K HE Hkc HK0 HKb) as HK.
  pose proof (rd_buf_facts E ac A HE Hac HA0 HAb) as HA.
  pose proof (rd_lenv_facts E HE) as (HS & Hm1 & Hm2 & Hm3 & _).
  assert (HK' : (K = 0 /\ rd_cap kc = 0) \/ (rd_cap kc = kc /\ apart K (kc + 1) (e_md E) MD_SIZE)).
  { destruct HK as [(_ & E1 & E2) | (_ & E1 & _ & _ & _ & H & _)]; [left | right]; split; assumption. }
  assert (HA' : (A = 0 /\ rd_cap ac = 0) \/ (rd_cap ac = ac /\ apart A (ac + 1) (e_md E) MD_SIZE)).
  { destruct HA as [(_ & E1 & E2) | (_ & E1 & _ & _ & _ & H & _)]; [left | right]; split; assumption. }
  clear - HS Hm1 Hm2 Hm3 HK' HA' Hkc Hac. cbn [disjoint_from rd_Wa]. rd_consts. repeat split; lia.
Qed.

Lemma rd_disj_gnl_m : forall E kc ac, lenv_ok E -> 0 <= kc < 40 -> 0 <= ac < 40 ->
  disjoint_from (rd_Wm E kc ac) A_G_NL NK_SIZE.
Proof.
  intros E kc ac HE Hkc Hac. pose proof (rd_lenv_facts E HE) as (HS & Hm1 & Hm2 & Hm3 & _).
  assert (0 <= rd_cap kc <= kc /\ 0 <= rd_cap ac <= ac) by (unfold rd_cap; destruct (kc =? 0), (ac =? 0); lia).
  clear - HS Hm1 Hm2 Hm3 H Hkc Hac. cbn [disjoint_from rd_Wm]. rd_consts. repeat split; lia.
Qed.

(* the first byte of a frame buffer model_read does not write *)
Lemma rd_disj_wk0 : forall E ac, lenv_ok E -> 0 <= ac < 40 ->
  disjoint_from (rd_Wm E 0 ac) (e_S E - SLOT_FRAME + FO_B256) 1.
Proof.
  intros E ac HE Hac. pose proof (rd_lenv_facts E HE) as (HS & Hm1 & Hm2 & Hm3 & _).
  assert (0 <= rd_cap ac <= ac) by (unfold rd_cap; destruct (ac =? 0); lia).
  clear - HS Hm1 Hm2 Hm3 H Hac. cbn [disjoint_from rd_Wm]. unfold rd_cap at 1. cbn [Z.eqb]. rd_consts.
  repeat split; lia.
Qed.

Lemma rd_disj_wa0 : forall E kc, lenv_ok E -> 0 <= kc < 40 ->
  disjoint_from (rd_Wm E kc 0) (e_S E - SLOT_FRAME + FO_B40) 1.
Proof.
  intros E kc HE Hkc. pose proof (rd_lenv_facts E HE) as (HS & Hm1 & Hm2 & Hm3 & _).
  assert (0 <= rd_cap kc <= kc) by (unfold rd_cap; destruct (kc =? 0); lia).
  clear - HS Hm1 Hm2 Hm3 H Hkc. cbn [disjoint_from rd_Wm]. unfold rd_cap at 2. cbn [Z.eqb]. rd_consts.
  repeat split; lia.
Qed.

(* the footprint the segment states *)
Lemma rd_seg_fp : forall E kc K ac A m0 m', rd_env E kc K ac A ->
  munch (rd_W E kc K ac A) m0 m' -> wmono rsegs m0 m' -> seg_fp (e_S E) (c0_hpKA E kc K ac A) m0 m'.
Proof.
  intros E kc K ac A m0 m' HENV MU WM. exists (rd_W E kc K ac A). split; [exact MU|]. split; [exact WM|].
  intros x Hx HO. destruct (rd_not_outside _ _ HO) as (lo & hi & Hin & Hr).
  destruct HENV as (HE & Hkc & Hac & HK0 & HA0 & HKb & HAb & _).
  pose proof (rd_buf_facts E kc K HE Hkc HK0 HKb) as HK.
  pose proof (rd_buf_facts E ac A HE Hac HA0 HAb) as HA.
  unfold rd_W in Hin. cbn [In] in Hin. unfold own_w, c0_hpKA, c0_hp2, c0_opt.
  destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; inversion E1; subst lo hi; clear E1.
  - left. unfold SLOT_STACK_Z, SLOT_FRAME in *. lia.
  - left. unfold SLOT_STACK_Z, SLOT_FRAME, FO_B40, FO_B256 in *. lia.
  - right; right; right; right; right. exists (e_md E), MD_SIZE. split; [left; reflexivity | lia].
  - right; left. unfold NK_N_SENT, NK_SIZE in *. lia.
  - right; right; right; right; left. lia.
  - destruct HK as [(_ & _ & E2) | (E0 & E2 & _)]; rewrite E2 in Hr; [lia|].
    right; right; right; right; right. exists K, (kc + 1).
    replace (kc =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0).
    split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity | lia].
  - destruct HA as [(_ & _ & E2) | (E0 & E2 & _)]; rewrite E2 in Hr; [lia|].
    right; right; right; right; right. exists A, (ac + 1).
    replace (ac =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0).
    split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | lia].
Qed.

(* the interface table across the segment's writes *)
Lemma rd_iftab_keep : forall E kc K ac A m m' kbs, rd_env E kc K ac A ->
  munch (rd_W E kc K ac A) m m' -> iftab_at m kbs link_tab -> ifptrs_at m -> iftab_at m' kbs link_tab.
Proof.
  intros E kc K ac A m m' kbs HENV MU IT IP.
  apply (c0_iftab_keep _ m m' kbs IT IP MU).
  - apply c0_out_disj, rd_disj_img; [exact HENV | | | | |]; unfold A_G_NL, NK_IF_NAME, NK_N_SENT, A_ERRNO, A_TP, ERRNO_TP_OFF; lia.
  - apply c0_out_disj, rd_disj_img; [exact HENV | | | | |]; unfold A_G_NL, NK_IF_INDEX, NK_N_SENT, A_ERRNO, A_TP, ERRNO_TP_OFF; lia.
  - split; apply c0_out_disj, rd_disj_img; try exact HENV;
      unfold A_RO_LO, A_RO_END, A_G_NAMES, G_NAMES_SIZE, A_G_NL, NK_N_SENT, A_ERRNO, A_TP, ERRNO_TP_OFF; lia.
Qed.


(* the writes before the alias reader: the two memsets and model_read *)
Definition rd_W03 (E : lenv) : list ivl :=
  [(e_S E - SLOT_STACK_Z, e_S E - SLOT_FRAME); (e_S E - SLOT_FRAME + FO_B40, e_S E - SLOT_FRAME + FO_B256 + 40);
   (e_md E, e_md E + MD_SIZE)].

Lemma rd_sub03_wk : forall E, sub_fp [(e_S E - SLOT_FRAME + FO_B256, e_S E - SLOT_FRAME + FO_B256 + 40)] (rd_W03 E).
Proof.
  intros E x Hx. cbn [outside rd_W03] in *. destruct Hx as (_ & X & _).
  split; [|exact I]. intros C. apply X. rd_consts. lia.
Qed.

Lemma rd_sub03_wa : forall E, sub_fp [(e_S E - SLOT_FRAME + FO_B40, e_S E - SLOT_FRAME + FO_B40 + 40)] (rd_W03 E).
Proof.
  intros E x Hx. cbn [outside rd_W03] in *. destruct Hx as (_ & X & _).
  split; [|exact I]. intros C. apply X. rd_consts. lia.
Qed.

Lemma rd_sub03_m : forall E kc ac, 0 <= kc < 40 -> 0 <= ac < 40 -> sub_fp (rd_Wm E kc ac) (rd_W03 E).
Proof.
  intros E kc ac Hk Ha x Hx. cbn [outside rd_W03 rd_Wm] in *.
  assert (0 <= rd_cap kc <= kc /\ 0 <= rd_cap ac <= ac) by (unfold rd_cap; destruct (kc =? 0), (ac =? 0); lia).
  rd_consts. destruct Hx as (X1 & X2 & X3 & _). repeat split; lia.
Qed.

Lemma rd_disj03_buf : forall E c B, lenv_ok E -> 0 <= c < 40 -> (c = 0 -> B = 0) -> (c <> 0 -> c0_blk E B (c + 1)) ->
  c <> 0 -> disjoint_from (rd_W03 E) B (c + 1).
Proof.
  intros E c B HE Hc H0 Hb Hn.
  destruct (rd_buf_facts E c B HE Hc H0 Hb) as [(E0 & _) | (_ & _ & B1 & B2 & B3 & B4 & _)]; [contradiction|].
  pose proof (rd_lenv_facts E HE) as (HS & _).
  clear - HS B1 B2 B3 B4 Hc. cbn [disjoint_from rd_W03]. rd_consts. repeat split; lia.
Qed.

(* ==========================================================================
   7. The walk
   ========================================================================== *)

Section Walk.
Hypothesis MEMSET_C : memset_contract.
Hypothesis MR : model_read_contract.
Hypothesis AR : reac_link_alias_read_contract.

Lemma c0_s3a : forall E i gp P N sel kc ac K A kbs mbs gbs ms,
    lenv_ok E -> c0_ret_ac E i gp P N sel kc ac K A kbs mbs gbs ms ->
    evt rsegs (eqv_cl (fun ms' => (exists kbs' mbs' op0 want rc,
                 c0_mid E i gp P N sel kc ac K A op0 want rc kbs' mbs' gbs ms') /\
                 seg_fp (e_S E) (c0_hpKA E kc K ac A) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp P N sel kc ac K A kbs mbs gbs ms HE HR.
  destruct HR as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & t3 & t4 & t5 & t6 & F & fc & m0
    & wa0 & wk0 & -> & FRM & Hi & Hsel & Hkc & Hac & HN & HKr & HAr & Hop & HKA & BK & BA & FR & BS & BG).
  change (ms_mem (MS _ _ _ _ _ m0 _)) with m0.
  assert (HENV : rd_env E kc K ac A).
  { destruct BK as (BK1 & BK2). destruct BA as (BA1 & BA2).
    split; [exact HE|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact BK1|]. split; [exact BA1|].
    split; [intros H; exact (proj1 (proj2 (BK2 H)))|]. split; [intros H; exact (proj1 (proj2 (BA2 H)))|].
    exact HKA. }
  pose proof (rd_lenv_facts E HE) as (LS & LM1 & LM2 & _).
  pose proof (rd_sel_ptr_rng sel Hsel) as Hsp.
  destruct (rd_frame_split E P N wa0 wk0 m0 FR) as (j0 & j2 & FPRE & FWA & FWK & FPOST).
  pose proof BS as (SV & NL & NW & IT & NO & NM & GN & OD & PR & LA & TX & IP & MA & MW & KA & KW & KR & CU
    & ER & GU & MI0 & TM0 & ST0).
  pose proof BG as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  pose proof NW as NW'. destruct NW' as (_ & _ & _ & _ & _ & (Hop1 & Hop2) & _).
  unfold C0_RA_AC, wz.
  step. step. step. step. step.
  (* memset (sp+0x78, 0, 40) *)
  eapply evt_cut.
  { eapply MEMSET_C; [| exact MI0].
    rewrite !unsigned_lit by (unfold SLOT_FRAME in *; lia). unfold FO_B256 in FWK. exact FWK. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
    & -> & MU1 & WM1 & MI1 & RW1).
  rewrite !unsigned_lit in MU1, RW1 by (unfold SLOT_FRAME in *; lia).
  replace (ret_pc (Z_to_bv 64 81520)) with (Z_to_bv 64 81520) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* memset (sp+0x50, 0, 40) *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MEMSET_C; [| exact MI1].
    rewrite !unsigned_lit by (unfold SLOT_FRAME in *; lia).
    eapply (rw_cells_transport rsegs); [exact FWA | exact MU1 | exact WM1|].
    cbn [disjoint_from cells_size csize]. unfold FO_B40, SLOT_FRAME. lia. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2
    & -> & MU2 & WM2 & MI2 & RW2).
  rewrite !unsigned_lit in MU2, RW2 by (unfold SLOT_FRAME in *; lia).
  replace (ret_pc (Z_to_bv 64 81536)) with (Z_to_bv 64 81536) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* the memory at the call of model_read *)
  assert (MU02 : munch (rd_W E kc K ac A) m0 m2).
  { eapply munch_trans; [eapply munch_weaken; [apply rd_sub_wk | exact MU1]
                        | eapply munch_weaken; [apply rd_sub_wa | exact MU2]]. }
  assert (WM02 : wmono rsegs m0 m2) by (eapply wmono_trans; eassumption).
  assert (NL2 : nlk_at m2 kbs).
  { eapply (c0_nlk_keep _ m1 m2 kbs); [eapply (c0_nlk_keep _ m0 m1 kbs NL MU1 WM1) | exact MU2 | exact WM2 |];
      apply c0_out_disj; cbn [disjoint_from]; c0_unf; lia. }
  assert (MA2 : model_at m2 (e_md E) mbs).
  { eapply (c0_model_keep _ m1 m2 _ mbs); [eapply (c0_model_keep _ m0 m1 _ mbs MA MU1 WM1) | exact MU2 | exact WM2 |];
      apply c0_out_disj; cbn [disjoint_from]; c0_unf; lia. }
  assert (ST2 : stk rsegs m2 (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME)).
  { eapply (stk_transport_disjoint rsegs); [eapply (stk_transport_disjoint rsegs); [exact ST0 | exact MU1 | exact WM1 |]
      | exact MU2 | exact WM2 |]; cbn [disjoint_from]; unfold SLOT_FRAME, SLOT_STACK_Z, FO_B40, FO_B256 in *; lia. }
  assert (IT2 : iftab_at m2 kbs link_tab) by exact (rd_iftab_keep E kc K ac A m0 m2 kbs HENV MU02 IT IP).
  assert (BS2 : c0_base E P N kbs mbs gbs m2)
    by exact (rd_base_keep E P N kbs mbs gbs kbs mbs kc K ac A m0 m2 HENV BS MU02 WM02 MI2 ST2 NL2 NW IT2 NO NM
                MA2 MW KR).
  assert (RW1' : rw_cells rsegs m2 (e_S E - SLOT_FRAME + 120)
                   [CB (Z.to_nat 40) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 40))]).
  { eapply (rw_cells_transport rsegs); [exact RW1 | exact MU2 | exact WM2|].
    cbn [disjoint_from cells_size csize]. unfold SLOT_FRAME. lia. }
  assert (FR2 : c0_frame E P N (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 40))
                  (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 40)) m2).
  { apply (rd_frame_join E P N j0 _ _ j2 m2).
    - apply (rd_keep_frame_cells E kc K ac A m0 m2 HENV MU02 WM02); [|exact FPRE].
      left. change (Z.of_nat (cells_size (rd_pre (e_md E) (e_mk E) P N j0))) with 80. unfold FO_B40. lia.
    - unfold FO_B40. exact RW2.
    - unfold FO_B256. exact RW1'.
    - apply (rd_keep_frame_cells E kc K ac A m0 m2 HENV MU02 WM02); [|exact FPOST].
      right. cbn [cells_size csize]. unfold FO_B256, SLOT_FRAME. lia. }
  (* lw s9, 0x218(s1): g_nl.opened *)
  assert (HR : ov_read_bytes rsegs m2 (wa (GNL40 + 536)) 4 = Some (le4 (Z_to_bv 64 (nk_opened kbs)))).
  { destruct NL2 as [NLa NLb]. unfold wa.
    exact (rd_u8arr_rd32 m2 A_G_NL kbs NK_OPENED (GNL40 + 536) NLa ltac:(unfold NK_OPENED; lia)
             ltac:(rewrite NLb; unfold NK_OPENED, NK_SIZE; lia) ltac:(unfold GNL40, NK_OPENED; lia)). }
  step. rewrite (rd_sx32 (nk_opened kbs)) by lia. clear HR.
  do 8 step.
  rewrite !rd_mask by (unfold SLOT_FRAME in *; lia).
  remember (if kc =? 0 then 0 else e_S E - SLOT_FRAME + 120) as k2 eqn:Ek2.
  remember (if ac =? 0 then 0 else e_S E - SLOT_FRAME + 80) as k4 eqn:Ek4.
  assert (K2 : (kc = 0 -> k2 = 0) /\ (kc <> 0 -> k2 = e_S E - SLOT_FRAME + FO_B256) /\ 0 <= k2 < 2 ^ 64).
  { subst k2. unfold FO_B256. destruct (Z.eqb_spec kc 0); unfold SLOT_FRAME in *; repeat split; intros; lia. }
  assert (K4 : (ac = 0 -> k4 = 0) /\ (ac <> 0 -> k4 = e_S E - SLOT_FRAME + FO_B40) /\ 0 <= k4 < 2 ^ 64).
  { subst k4. unfold FO_B40. destruct (Z.eqb_spec ac 0); unfold SLOT_FRAME in *; repeat split; intros; lia. }
  clear Ek2 Ek4. destruct K2 as (K2a & K2b & K2r). destruct K4 as (K4a & K4b & K4r).
  do 5 step.
  (* model_read *)
  pose proof MR as MR'. rewrite c0_model_read_is in MR'.
  eapply (leaf_call _ _ _ _ _ MR' c0_model_read_post_ext) with (lo := e_S E - SLOT_STACK_Z);
    [ apply rd_q_ext | | exact MI2
    | rewrite unsigned_lit by (unfold SLOT_FRAME in *; lia); exact ST2
    | rewrite unsigned_lit by (unfold SLOT_FRAME in *; lia); unfold SLOT_FRAME, SLOT_STACK_Z; lia
    | rewrite unsigned_lit by (unfold SLOT_FRAME in *; lia); unfold SLOT_FRAME in *; lia | ].
  { pose proof BS2 as (_ & _ & _ & _ & _ & _ & GN2 & OD2 & _ & _ & _ & IP2 & _).
    eapply (c0_model_read_pre E _ m2 P N _ _ sel kc ac kbs mbs HE);
      rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5;
      rewrite ?unsigned_lit by (unfold SLOT_FRAME in *; lia); try lia; eassumption. }
  intros ra3 t03 t13 t23 a03 a13 a23 a33 a43 a53 a63 a73 t33 t43 t53 t63 m3 MU3 WM3 MI3 ST3 PO3.
  replace (ret_pc (Z_to_bv 64 81592)) with (Z_to_bv 64 81592) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  unfold c0_model_read_Wr, c0_model_read_Post in MU3, PO3. cbv beta in MU3, PO3.
  rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5 in MU3.
  rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?rd_getr10 in PO3.
  rewrite ?unsigned_lit in MU3 by (unfold SLOT_FRAME in *; lia).
  rewrite ?unsigned_lit in PO3 by (unfold SLOT_FRAME in *; lia).
  rewrite ?unsigned_lit in ST3 by (unfold SLOT_FRAME in *; lia).
  apply (munch_weaken _ (rd_Wm E kc ac)) in MU3; [| exact (rd_sub_mcall E kc ac k2 k4 HE Hkc Hac K2a K2b K4a K4b)].
  pose proof BS2 as (_ & _ & _ & _ & _ & _ & GN2 & OD2 & _ & _ & _ & IP2 & _).
  specialize (PO3 mbs kbs link_tab (sel_name sel) MA2 NL2 IT2 (c0_sel_str m2 sel Hsel GN2 OD2)).
  rewrite (rd_md_reqs0 mbs B4), (rd_kstate kbs mbs BG) in PO3.
  destruct PO3 as (RC3 & (mbs' & MA3 & MW3 & _ & _ & _ & MQ3 & MNq3 & MMk3 & MMs3) & CK3 & CA3 & JK3 & JA3).
  subst a03.
  (* the memory at the call of the alias reader *)
  assert (MU03 : munch (rd_W E kc K ac A) m0 m3)
    by (eapply munch_trans; [exact MU02 | eapply (munch_weaken (rd_Wm E kc ac)); [apply rd_sub_m; assumption | exact MU3]]).
  assert (WM03 : wmono rsegs m0 m3) by (eapply wmono_trans; eassumption).
  assert (MU03' : munch (rd_W03 E) m0 m3).
  { eapply munch_trans; [eapply munch_trans; [eapply munch_weaken; [apply rd_sub03_wk | exact MU1]
                                            | eapply munch_weaken; [apply rd_sub03_wa | exact MU2]]
                        | eapply (munch_weaken (rd_Wm E kc ac)); [apply rd_sub03_m; assumption | exact MU3]]. }
  assert (NL3 : nlk_at m3 kbs)
    by exact (c0_nlk_keep _ m2 m3 kbs NL2 MU3 WM3 (c0_out_disj _ _ _ (rd_disj_gnl_m E kc ac HE Hkc Hac))).
  assert (IT3 : iftab_at m3 kbs link_tab).
  { apply (rd_iftab_keep E kc K ac A m2 m3 kbs HENV); [| exact IT2 | exact IP2].
    eapply (munch_weaken (rd_Wm E kc ac)); [apply rd_sub_m; assumption | exact MU3]. }
  assert (KR3 : marks_are gbs mbs') by (destruct KR as [KR1 KR2]; split; [rewrite MMk3; exact KR1 | rewrite MMs3; exact KR2]).
  assert (BS3 : c0_base E P N kbs mbs' gbs m3)
    by exact (rd_base_keep E P N kbs mbs gbs kbs mbs' kc K ac A m0 m3 HENV BS MU03 WM03 MI3 ST3 NL3 NW IT3 NO NM
                MA3 MW3 KR3).
  pose proof BS3 as (_ & _ & _ & _ & _ & _ & GN3 & OD3 & _ & _ & _ & IP3 & _ & _ & _ & _ & _ & _ & ER3 & _).
  assert (BK3 : c0_buf E kc K m3).
  { apply (c0_buf_keep _ m0 m3 E kc K BK MU03' WM03 ltac:(lia)). intros Hn.
    apply c0_out_disj. destruct BK as [BK1 BK2].
    exact (rd_disj03_buf E kc K HE Hkc BK1 (fun H => proj1 (proj2 (BK2 H))) Hn). }
  assert (BA3 : c0_buf E ac A m3).
  { apply (c0_buf_keep _ m0 m3 E ac A BA MU03' WM03 ltac:(lia)). intros Hn.
    apply c0_out_disj. destruct BA as [BA1 BA2].
    exact (rd_disj03_buf E ac A HE Hac BA1 (fun H => proj1 (proj2 (BA2 H))) Hn). }
  (* the two frame buffers model_read left *)
  assert (FK3 : cstr_at m3 (e_S E - SLOT_FRAME + FO_B256)
                  (if kc <? 1 then [] else r_kind (read_core link_tab (sel_name sel) kc ac [] (nk_kstate kbs)))).
  { destruct (Z.eqb_spec kc 0) as [E0|E0].
    - subst kc. change (0 <? 1) with true. cbv iota.
      apply (c0_cstr_keep _ m2 m3 _ [] (rd_cstr_nil m2 _ _ _ RW1' eq_refl) MU3).
      apply c0_out_disj. exact (rd_disj_wk0 E ac HE Hac).
    - replace (kc <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite <- (K2b E0). apply CK3; [rewrite (K2b E0); unfold FO_B256, SLOT_FRAME in *; lia | lia]. }
  assert (FA3 : cstr_at m3 (e_S E - SLOT_FRAME + FO_B40)
                  (if ac <? 1 then [] else r_alias (read_core link_tab (sel_name sel) kc ac [] (nk_kstate kbs)))).
  { destruct (Z.eqb_spec ac 0) as [E0|E0].
    - subst ac. change (0 <? 1) with true. cbv iota.
      assert (C2 : cstr_at m2 (e_S E - SLOT_FRAME + FO_B40) []) by exact (rd_cstr_nil m2 _ _ _ RW2 eq_refl).
      apply (c0_cstr_keep _ m2 m3 _ [] C2 MU3).
      apply c0_out_disj. exact (rd_disj_wa0 E kc HE Hkc).
    - replace (ac <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite <- (K4b E0). apply CA3; [rewrite (K4b E0); unfold FO_B40, SLOT_FRAME in *; lia | lia]. }
  clear CK3 CA3 JK3 JA3.
  do 7 step.
  (* reac_link_alias_read *)
  pose proof AR as AR'. rewrite c0_alias_read_is in AR'.
  eapply (leaf_call _ _ _ _ _ AR' c0_alias_read_post_ext) with (lo := e_S E - SLOT_STACK_Z);
    [ apply rd_q_ext | | exact MI3
    | rewrite unsigned_lit by (unfold SLOT_FRAME in *; lia); exact ST3
    | rewrite unsigned_lit by (unfold SLOT_FRAME in *; lia); unfold SLOT_FRAME, SLOT_STACK_Z; lia
    | rewrite unsigned_lit by (unfold SLOT_FRAME in *; lia); unfold SLOT_FRAME in *; lia | ].
  { eapply (c0_alias_read_pre E _ m3 sel kc ac K A i kbs HE);
      rewrite ?mkR_sp, ?mkR_errno, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4;
      rewrite ?unsigned_lit by (unfold SLOT_FRAME, A_TP in *; lia); try (unfold A_ERRNO; lia); try eassumption.
    }
  intros ra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 m4 MU4 WM4 MI4 ST4 PO4.
  replace (ret_pc (Z_to_bv 64 81620)) with (Z_to_bv 64 81620) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  unfold c0_alias_read_Wr, c0_alias_read_Post in MU4, PO4. cbv beta in MU4, PO4.
  rewrite ?mkR_sp, ?mkR_errno, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4 in MU4.
  rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?rd_getr10 in PO4.
  rewrite ?unsigned_lit in MU4 by (unfold SLOT_FRAME, A_TP in *; lia).
  rewrite ?unsigned_lit in PO4 by (unfold SLOT_FRAME in *; lia).
  rewrite ?unsigned_lit in ST4 by (unfold SLOT_FRAME in *; lia).
  apply (munch_weaken _ (rd_Wa E kc K ac A)) in MU4; [| exact (rd_sub_acall E kc K ac A HENV)].
  specialize (PO4 kbs link_tab (sel_name sel) NL3 IT3 (c0_sel_str m3 sel Hsel GN3 OD3)).
  rewrite (rd_nk_sent0 kbs B2) in PO4.
  destruct PO4 as (RC4 & (kbs' & NL4 & NW4 & _ & _ & _ & IT4 & _ & _ & _ & NQ4 & NNq4 & NO4 & NM4 & ND4 & (NB4 & NB4')
    & NF4) & CK4 & CA4 & JK4 & JA4).
  subst a04. unfold read_lib in CK4, CA4, NQ4, NNq4.
  (* the memory at 0x13ed4 *)
  assert (MU04 : munch (rd_W E kc K ac A) m0 m4)
    by (eapply munch_trans; [exact MU03 | eapply (munch_weaken (rd_Wa E kc K ac A)); [apply rd_sub_a | exact MU4]]).
  assert (WM04 : wmono rsegs m0 m4) by (eapply wmono_trans; eassumption).
  assert (MA4 : model_at m4 (e_md E) mbs')
    by exact (c0_model_keep _ m3 m4 _ _ MA3 MU4 WM4 (c0_out_disj _ _ _ (rd_disj_md_a E kc K ac A HENV))).
  assert (NM4' : nk_misuse kbs' = 0) by (rewrite NM4; exact NM).
  assert (BS4 : c0_base E P N kbs' mbs' gbs m4)
    by exact (rd_base_keep E P N kbs mbs gbs kbs' mbs' kc K ac A m0 m4 HENV BS MU04 WM04 MI4 ST4 NL4 NW4 IT4 NO4 NM4'
                MA4 MW3 KR3).
  assert (RQ4 : requests_are kbs' mbs').
  { apply c0_requests_are; [rewrite NQ4, MQ3; reflexivity | rewrite NNq4, MNq3; reflexivity | exact NW4 | exact MW3
      | exact (proj2 NL4) | exact (proj2 MA3)]. }
  assert (FR4 : exists wa' wk', c0_frame E P N wa' wk' m4).
  { destruct (c0_wr_rw m4 (e_S E - SLOT_FRAME + FO_B40) 40 (wr_at_transport rsegs m0 m4 _ _ (proj2 FWA) WM04)
                ltac:(lia)) as (wa' & WA4).
    destruct (c0_wr_rw m4 (e_S E - SLOT_FRAME + FO_B256) 40 (wr_at_transport rsegs m0 m4 _ _ (proj2 FWK) WM04)
                ltac:(lia)) as (wk' & WK4).
    exists wa', wk'. apply (rd_frame_join E P N j0 wa' wk' j2 m4).
    - apply (rd_keep_frame_cells E kc K ac A m0 m4 HENV MU04 WM04); [|exact FPRE].
      left. change (Z.of_nat (cells_size (rd_pre (e_md E) (e_mk E) P N j0))) with 80. unfold FO_B40. lia.
    - exact WA4.
    - exact WK4.
    - apply (rd_keep_frame_cells E kc K ac A m0 m4 HENV MU04 WM04); [|exact FPOST].
      right. cbn [cells_size csize]. unfold FO_B256, SLOT_FRAME. lia. }
  destruct FR4 as (wa' & wk' & FR4).
  pose proof (c0_rkind_len link_tab (sel_name sel) kc ac [] (nk_kstate kbs) ltac:(lia)) as LK.
  pose proof (c0_ralias_len link_tab (sel_name sel) kc ac [] (nk_kstate kbs) ltac:(lia)) as LA'.
  assert (FK4 : cstr_at m4 (e_S E - SLOT_FRAME + FO_B256)
                  (if kc <? 1 then [] else r_kind (read_core link_tab (sel_name sel) kc ac [] (nk_kstate kbs)))).
  { apply (c0_cstr_keep _ m3 m4 _ _ FK3 MU4). apply c0_out_disj.
    apply rd_disj_frame_a; [exact HENV | lia | unfold FO_B256; lia |].
    destruct (kc <? 1); cbn [length Z.of_nat]; unfold FO_B256, SLOT_FRAME in *; lia. }
  assert (FA4 : cstr_at m4 (e_S E - SLOT_FRAME + FO_B40)
                  (if ac <? 1 then [] else r_alias (read_core link_tab (sel_name sel) kc ac [] (nk_kstate kbs)))).
  { apply (c0_cstr_keep _ m3 m4 _ _ FA3 MU4). apply c0_out_disj.
    apply rd_disj_frame_a; [exact HENV | lia | unfold FO_B40; lia |].
    destruct (ac <? 1); cbn [length Z.of_nat]; unfold FO_B40, SLOT_FRAME in *; lia. }
  (* the texts in the two heap buffers *)
  assert (TK4 : kc <> 0 -> cstr_at m4 K (r_kind (read_core link_tab (sel_name sel) kc ac [] (nk_kstate kbs))) /\
                  exists bs, tbuf_at m4 K kc bs /\ In (zb 0) bs).
  { intros Hk. destruct BK as [BK1 BK2]. destruct (BK2 Hk) as (Kn0 & Kblk & KT).
    pose proof (CK4 Kn0 ltac:(lia)) as C4. destruct (JK4 Kn0 ltac:(lia)) as (junk & J4).
    split; [exact C4|].
    pose proof (rd_guard_of m0 K kc _ ltac:(lia) KT) as G0.
    assert (G4 : rw_cells rsegs m4 (K + kc) [C1 (zb GUARD_BYTE)]).
    { apply (c0_rw_keep _ m0 m4 _ _ G0 MU04 WM04). apply c0_out_disj. exact (rd_disj_kguard E kc K ac A HENV Hk). }
    exists junk. split; [exact (rd_tbuf m4 K kc junk ltac:(lia) J4 G4)|].
    apply (c0_cstr_in_cb m4 K _ (Z.to_nat kc) junk C4 J4). lia. }
  assert (TA4 : ac <> 0 -> cstr_at m4 A (r_alias (read_core link_tab (sel_name sel) kc ac [] (nk_kstate kbs))) /\
                  exists bs, tbuf_at m4 A ac bs /\ In (zb 0) bs).
  { intros Ha. destruct BA as [BA1 BA2]. destruct (BA2 Ha) as (An0 & Ablk & AT).
    pose proof (CA4 An0 ltac:(lia)) as C4. destruct (JA4 An0 ltac:(lia)) as (junk & J4).
    split; [exact C4|].
    pose proof (rd_guard_of m0 A ac _ ltac:(lia) AT) as G0.
    assert (G4 : rw_cells rsegs m4 (A + ac) [C1 (zb GUARD_BYTE)]).
    { apply (c0_rw_keep _ m0 m4 _ _ G0 MU04 WM04). apply c0_out_disj. exact (rd_disj_aguard E kc K ac A HENV Ha). }
    exists junk. split; [exact (rd_tbuf m4 A ac junk ltac:(lia) J4 G4)|].
    apply (c0_cstr_in_cb m4 A _ (Z.to_nat ac) junk C4 J4). lia. }
  (* the cut *)
  apply evt_done. apply c0_eqv_intro. split; [| exact (rd_seg_fp E kc K ac A m0 m4 HENV MU04 WM04)].
  exists kbs', mbs', (nk_opened kbs), (norm_rc (r_rc (read_core link_tab (sel_name sel) kc ac [] (nk_kstate kbs)))),
    (r_rc (read_core link_tab (sel_name sel) kc ac [] (nk_kstate kbs))).
  unfold c0_mid.
  exists ra4, t04, t14, t24, a14, a24, a34, a44, a54, a64, a74, (Z_to_bv 64 171), t34, t44, t54, t64, F, fc, m4,
    wa', wk'.
  split; [reflexivity|].
  split; [exact FRM|]. split; [exact Hi|]. split; [exact Hsel|]. split; [exact Hkc|]. split; [exact Hac|].
  split; [exact HN|]. split; [exact HKr|]. split; [exact HAr|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [exact HKA|].
  exists kbs. cbv zeta.
  split; [exact NW|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact NF4|].
  split; [exact TK4|]. split; [exact TA4|]. split; [exact FK4|]. split; [exact FA4|].
  split; [intros Hk; exact (proj1 (proj2 (proj2 BK Hk)))|].
  split; [intros Ha; exact (proj1 (proj2 (proj2 BA Ha)))|].
  split; [exact (proj1 BK)|]. split; [exact (proj1 BA)|].
  split; [exact RQ4|]. split; [exact FR4 | exact BS4].
Qed.

End Walk.
