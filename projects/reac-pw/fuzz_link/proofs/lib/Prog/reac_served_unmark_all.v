(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/L_hkit.v, with its module paths and module names changed; 801 of its 858 lines of code are new or changed and 196 lines of the source are left out. *)
(* reac_served_unmark_all (reac_served_mark.c:94-107), PLAIN build: the walk of its contract
   (lib/Prog/reac_served_unmark_all_c.v) on the plain image, entry 0x16770.

   a0 = NULL: `beqz a0` goes straight to `ret`. Otherwise a 0x130-byte frame, n read from 0(m), and
   for i < n (n re-read after each round, 0x167f0): reac_link_alias_read(name_i, NULL, 0, sp, 256)
   at 0x167c8, then on 0 bcmp(sp, "reac-pw:served", 15) at 0x167dc, then on 0
   reac_link_alias_write(name_i, "") at 0x167ec; last memset(m, 0, 516) at 0x1680c.
   The loop is `head_all` (induction on the rounds left) over `body_ok` (one round, 0x167b4 to
   0x167f0) and `join_ok` (0x167f0 to the next head or to the tail); `inv` is the state at the
   head: the fake kernel as link_spec's `unmark_walk` has left it after c names (`kinv`) and the
   memory the loop keeps (`minv`). The two library calls are `leaf` contracts (mk_call.v
   `leaf_call`); bcmp and memset are called through their mkR-form contracts. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call mk_str mk_marks
  reac_served_unmark_all_c reac_link_alias_read_c reac_link_alias_write_c bcmp_c memset_c bcmp memset.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
From Stdlib Require Import FunctionalExtensionality.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Pure facts
   ========================================================================== *)

Lemma signed_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit by lia.
  apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

(* bcmp(buf, "reac-pw:served", 15) over a C string in buf: it stops at the first difference,
   which comes at the latest at the string's NUL, so 15 bytes of the policy string suffice *)
Lemma memcmp_served_walk : forall p s, ~ In (zb 0) s -> ~ In (zb 0) p ->
  exists v, memcmp_model (s ++ [zb 0]) (p ++ [zb 0]) (S (length p)) = Some v /\ -256 < v < 256 /\
            (v = 0 <-> s = p).
Proof.
  induction p as [|b p IH]; intros s Ns Np.
  - destruct s as [|a s].
    + exists 0. split; [reflexivity|]. split; [lia|]. tauto.
    + assert (Ha : bv_unsigned a <> 0) by (intros E; apply Ns; left; apply byte_zero; exact E).
      pose proof (byte_range a) as Ra.
      exists (bv_unsigned a - bv_unsigned (zb 0)). split.
      * cbn [app memcmp_model length].
        replace (bv_unsigned a =? bv_unsigned (zb 0)) with false; [reflexivity|].
        symmetry. apply Z.eqb_neq. rewrite bz_zb0. exact Ha.
      * rewrite bz_zb0. split; [lia|]. split; [lia | discriminate].
  - assert (Hb : bv_unsigned b <> 0) by (intros E; apply Np; left; apply byte_zero; exact E).
    pose proof (byte_range b) as Rb.
    destruct s as [|a s].
    + exists (bv_unsigned (zb 0) - bv_unsigned b). split.
      * cbn [app memcmp_model length].
        replace (bv_unsigned (zb 0) =? bv_unsigned b) with false; [reflexivity|].
        symmetry. apply Z.eqb_neq. rewrite bz_zb0. lia.
      * rewrite bz_zb0. split; [lia|]. split; [lia | discriminate].
    + assert (Ha : bv_unsigned a <> 0) by (intros E; apply Ns; left; apply byte_zero; exact E).
      pose proof (byte_range a) as Ra.
      destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Eab|Nab].
      * apply byte_eq in Eab. subst b.
        destruct (IH s (fun H => Ns (or_intror H)) (fun H => Np (or_intror H))) as (v & Hv & Rv & Iv).
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

Lemma bcmp_served : forall s, ~ In (zb 0) s ->
  exists v, memcmp_model (s ++ [zb 0]) (S_SERVED ++ [zb 0]) 15 = Some v /\ -256 < v < 256 /\
            (v = 0 <-> bl_eqb s S_SERVED = true).
Proof.
  intros s Ns. destruct (memcmp_served_walk S_SERVED s Ns S_SERVED_no_nul) as (v & Hv & Rv & Iv).
  exists v. split; [exact Hv|]. split; [exact Rv|]. rewrite bl_eqb_iff. exact Iv.
Qed.

Lemma skipn_nth : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn [skipn]. apply IH. exact H.
Qed.

Lemma munch_sym : forall W m m', munch W m m' -> munch W m' m.
Proof. intros W m m' H x Hx. symmetry. apply H, Hx. Qed.

Lemma disjoint_from_sub : forall W a n b k, disjoint_from W a n -> a <= b -> b + k <= a + n ->
  disjoint_from W b k.
Proof.
  induction W as [|[l h] W IH]; intros a n b k H H1 H2; cbn in *; [exact I|].
  destruct H as [H0 H]. split; [lia|]. exact (IH a n b k H H1 H2).
Qed.

Lemma bytes_at_back : forall W m m' a bs, bytes_at rsegs m' a bs -> munch W m m' ->
  disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs m a bs.
Proof. intros W m m' a bs H MU D. exact (bytes_at_transport rsegs W m' m a bs H (munch_sym W m m' MU) D). Qed.

Lemma wr_at_app' : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m a (n1 + n2) <-> wr_at rsegs m a n1 /\ wr_at rsegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app_iff : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app' by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

(* `stk` survives a call that rewrote part of it, when what it rewrote is still readable cells *)
Lemma stk_transport_rw : forall W m m' lo hi A cs,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' -> rw_cells rsegs m' A cs ->
  (forall x, lo <= x < hi -> outside W x \/ A <= x < A + Z.of_nat (cells_size cs)) ->
  stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi A cs (H1 & H2 & H) MU WM [[Hwf Hb] Hw] Hc.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (Hc a Ha) as [Ho|Hin].
  - destruct (H a Ha) as [Hv [b Hr]]. split; [apply WM; exact Hv|].
    exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hr|]. rewrite wa_unsigned by lia. exact Ho.
  - destruct Hw as (_ & _ & Hw). split.
    + replace a with (A + (a - A)) by lia. apply Hw. lia.
    + destruct Hb as (_ & _ & Hb). rewrite (cells_bytes_length cs Hwf) in Hb.
      specialize (Hb (Z.to_nat (a - A)) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
      replace (A + (a - A)) with a in Hb by lia. rewrite Hb.
      destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
      apply nth_error_None in E. rewrite (cells_bytes_length cs Hwf) in E. lia.
Qed.

(* ---- uniqueness of the views ---- *)

Lemma u8arr_unique : forall m a l1 l2, u8arr rsegs m a l1 -> u8arr rsegs m a l2 ->
  length l1 = length l2 -> l1 = l2.
Proof. intros m a l1 l2 [B1 _] [B2 _] L. exact (bytes_at_unique m a l1 l2 B1 B2 L). Qed.

Lemma nlk_unique : forall m k1 k2, nlk_at m k1 -> nlk_at m k2 -> k1 = k2.
Proof. intros m k1 k2 [U1 L1] [U2 L2]. apply (u8arr_unique m A_G_NL); [exact U1 | exact U2 | lia]. Qed.

Lemma marks_unique : forall m a g1 g2, marks_at m a g1 -> marks_at m a g2 -> g1 = g2.
Proof. intros m a g1 g2 [U1 L1] [U2 L2]. apply (u8arr_unique m a); [exact U1 | exact U2 | lia]. Qed.

Lemma u64_at_unique : forall m a p1 p2, u64_at m a p1 -> u64_at m a p2 -> p1 mod 2 ^ 64 = p2 mod 2 ^ 64.
Proof.
  intros m a p1 p2 H1 H2. unfold u64_at in *.
  pose proof (bytes_at_unique m a _ _ H1 H2 ltac:(rewrite !length_le8; reflexivity)) as E.
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  unfold wz in E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_wrap in E. exact E.
Qed.

Lemma u32_at_unique : forall m a x1 x2, u32_at m a x1 -> u32_at m a x2 ->
  0 <= x1 < 2 ^ 31 -> 0 <= x2 < 2 ^ 31 -> x1 = x2.
Proof.
  intros m a x1 x2 H1 H2 R1 R2. unfold u32_at in *.
  pose proof (bytes_at_unique m a _ _ H1 H2 ltac:(rewrite !length_le4; reflexivity)) as E.
  apply (f_equal bytes_le_to_Z) in E. rewrite !bytes_le_to_Z_le4 in E. unfold wz in E.
  rewrite !unsigned_lit in E by lia. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma iftab_unique : forall m kbs t1 t2, iftab_at m kbs t1 -> iftab_at m kbs t2 -> t1 = t2.
Proof.
  intros m kbs t1 t2 (L1 & _ & H1) (L2 & _ & H2).
  apply nth_error_ext. intros i.
  destruct (nth_error t1 i) as [[n1 x1]|] eqn:E1; destruct (nth_error t2 i) as [[n2 x2]|] eqn:E2.
  - destruct (H1 i n1 x1 E1) as (R1 & p1 & U1 & P1 & C1 & X1).
    destruct (H2 i n2 x2 E2) as (R2 & p2 & U2 & P2 & C2 & X2).
    pose proof (u64_at_unique m _ p1 p2 U1 U2) as Ep.
    pose proof (bytes_at_bound _ _ _ _ (proj1 C1)) as B1. pose proof (bytes_at_bound _ _ _ _ (proj1 C2)) as B2.
    rewrite length_app in B1, B2. cbn [length] in B1, B2.
    rewrite !Z.mod_small in Ep by lia. subst p2.
    pose proof (cstr_at_unique m n1 p1 n2 C1 C2) as En. subst n2.
    rewrite (u32_at_unique m _ x1 x2 X1 X2 R1 R2). reflexivity.
  - apply nth_error_None in E2. assert (i < length t1)%nat by (apply nth_error_Some; congruence). lia.
  - apply nth_error_None in E1. assert (i < length t2)%nat by (apply nth_error_Some; congruence). lia.
  - reflexivity.
Qed.

(* the interface table survives a write set that misses the two arrays and every name string *)
Lemma iftab_transport : forall W m m' kbs tab,
  iftab_at m kbs tab -> munch W m m' ->
  disjoint_from W (A_G_NL + NK_IF_NAME) 640 -> disjoint_from W (A_G_NL + NK_IF_INDEX) 320 ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) -> u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
     disjoint_from W p (Z.of_nat (length n2) + 1)) ->
  iftab_at m' kbs tab.
Proof.
  intros W m m' kbs tab (L & B & H) MU D1 D2 DP. split; [exact L|]. split; [exact B|].
  intros i nm ix E. destruct (H i nm ix E) as (R & p & U & P & C & X). split; [exact R|]. exists p.
  assert (Hi : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  split; [|split; [exact P|split]].
  - unfold u64_at in *. apply (bytes_at_transport rsegs W m m' _ _ U MU). rewrite length_le8.
    apply (disjoint_from_sub _ _ _ _ _ D1); lia.
  - destruct C as [Cb Cn]. split; [|exact Cn]. apply (bytes_at_transport rsegs W m m' _ _ Cb MU).
    rewrite length_app. cbn [length]. replace (Z.of_nat (length nm + 1)) with (Z.of_nat (length nm) + 1) by lia.
    exact (DP i nm ix p E U).
  - unfold u32_at in *. apply (bytes_at_transport rsegs W m m' _ _ X MU). rewrite length_le4.
    apply (disjoint_from_sub _ _ _ _ _ D2); lia.
Qed.

(* ---- the fake kernel's state across the two library calls ---- *)

Lemma nk_kstate_eq : forall kbs K, nk_chunks kbs = k_chunks K -> nk_next kbs = Z.of_nat (k_next K) ->
  nk_end_errno kbs = k_end K -> nk_socket_errno kbs = k_sock K -> nk_send_errno kbs = k_send K ->
  nk_kstate kbs = K.
Proof.
  intros kbs [c n e s d] H1 H2 H3 H4 H5. cbn in *. unfold nk_kstate.
  rewrite H1, H2, H3, H4, H5, Nat2Z.id. reflexivity.
Qed.

Lemma talk_after_ce : forall K, k_chunks (talk_after K) = k_chunks K /\ k_end (talk_after K) = k_end K.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [split; reflexivity|].
  destruct (negb (k_send K =? 0)); [split; reflexivity|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  destruct v; split; reflexivity.
Qed.

Lemma read_state_ce : forall tab nm kc ac reqs K,
  k_chunks (r_state (read_core tab nm kc ac reqs K)) = k_chunks K /\
  k_end (r_state (read_core tab nm kc ac reqs K)) = k_end K.
Proof.
  intros. unfold read_core. destruct nm as [s|]; [|split; reflexivity]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|]. apply talk_after_ce.
Qed.

Lemma write_state_ce : forall tab nm al reqs K,
  k_chunks (w_state (write_core tab nm al reqs K)) = k_chunks K /\
  k_end (w_state (write_core tab nm al reqs K)) = k_end K.
Proof.
  intros. unfold write_core. destruct nm as [s|]; [|split; reflexivity].
  destruct al as [a|]; [|split; reflexivity]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|]. apply talk_after_ce.
Qed.

(* the 7 bytes after "" at A_EMPTY (0x10369..0x1036f, ".\0usage"): strlen's slack *)
Lemma empty_slack : forall m, mem_inv rsegs m ->
  bytes_at rsegs m (A_EMPTY + 0 + 1) (map (Z_to_bv 8) [46; 0; 117; 115; 97; 103; 101]).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold A_EMPTY; lia | cbn; unfold A_EMPTY; lia |].
  unfold A_EMPTY. vm_compute. repeat split; reflexivity.
Qed.

Lemma empty_ro : ro_addr rsegs (wa A_EMPTY) = true.
Proof. vm_compute. reflexivity. Qed.

(* a read-only byte is never inside a stack range *)
Lemma stk_not_ro : forall m lo hi a, mem_inv rsegs m -> stk rsegs m lo hi -> ro_addr rsegs (wa a) = true ->
  a < lo \/ hi <= a.
Proof.
  intros m lo hi a MI (H1 & H2 & H) R.
  destruct (Z.lt_ge_cases a lo) as [?|Hl]; [left; assumption|].
  destruct (Z.lt_ge_cases a hi) as [Hh|?]; [|right; assumption].
  exfalso. destruct (H a ltac:(lia)) as [Hw _]. apply Hw.
  unfold wview. destruct (m (wa a)) as [b|] eqn:E.
  - rewrite (MI _ _ E) in R. discriminate.
  - unfold ro_addr in R. destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [sg|]; [|discriminate].
    apply negb_true_iff in R. rewrite R. reflexivity.
Qed.

(* ---- the reader's answer is a small number ---- *)

Lemma rd32_range : forall c off, 0 <= rd32 c off < 2 ^ 32.
Proof.
  intros c off. unfold rd32, link_spec.rdn. pose proof (bytes_le_to_Z_nonneg (slice c off 4)) as H0.
  pose proof (bytes_le_to_Z_bound (slice c off 4)) as H1.
  assert (L : (length (slice c off 4) <= 4)%nat) by (unfold slice; rewrite length_firstn; lia).
  assert (P : 2 ^ (8 * Z.of_nat (length (slice c off 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  set (q := 2 ^ (8 * Z.of_nat (length (slice c off 4)))) in *. lia.
Qed.

Lemma rd32s_range : forall c off, - 2 ^ 31 <= rd32s c off < 2 ^ 31.
Proof.
  intros c off. unfold rd32s. cbv zeta. pose proof (rd32_range c off) as R.
  destruct (Z.ltb_spec (rd32 c off) (2 ^ 31)); lia.
Qed.

Lemma msg_scan_err : forall fuel c off left code, msg_scan fuel c off left = NlErr code ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction fuel as [|f IH]; intros c off left code H; cbn [msg_scan] in H; [discriminate|].
  destruct (left <? NL_HDR); [discriminate|].
  destruct ((rd32 c off <? NL_HDR) || (left <? rd32 c off)); [discriminate|].
  destruct (rd16 c (off + 4) =? NL_ERROR).
  - destruct (rd32 c off <? NL_HDR + NL_ERR_BODY); [discriminate|]. injection H as <-. apply rd32s_range.
  - destruct (rd16 c (off + 4) =? RTM_NEWLINK); [discriminate|]. exact (IH _ _ _ _ H).
Qed.

Lemma chunk_loop_err : forall fuel cs i code j, chunk_loop fuel cs i = (NlErr code, j) ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction fuel as [|f IH]; intros cs i code j H; cbn [chunk_loop] in H; [discriminate|].
  destruct (nth_error cs i) as [c|]; [|discriminate].
  destruct (chunk_walk c) as [| |code'|a] eqn:E.
  - exact (IH _ _ _ _ H).
  - discriminate.
  - injection H as <- _. exact (msg_scan_err _ _ _ _ _ E).
  - discriminate.
Qed.

Lemma talk_rc_range : forall K, 0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 32 < talk_rc_lib K < 2 ^ 32.
Proof.
  intros K Hs Hd He. unfold talk_rc_lib, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn [fst]; lia|].
  destruct (negb (k_send K =? 0)); [cbn [fst]; lia|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j] eqn:E.
  destruct v as [| |code|a]; simpl.
  - lia.
  - unfold E_IO. lia.
  - pose proof (chunk_loop_err _ _ _ _ _ E). lia.
  - lia.
Qed.

Lemma read_rc_range : forall tab nm kc ac reqs K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 32 < r_rc (read_core tab nm kc ac reqs K) < 2 ^ 32.
Proof.
  intros tab nm kc ac reqs K Hs Hd He. unfold read_core.
  destruct nm as [s|]; [|cbn [r_rc]; unfold E_INVAL; lia]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [cbn [r_rc]; unfold E_INVAL; lia|].
  destruct (index_of tab s =? 0); [cbn [r_rc]; unfold E_NODEV; lia|].
  cbn [r_rc]. apply talk_rc_range; assumption.
Qed.

Lemma lts_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_small by lia. reflexivity. Qed.

(* the register map the step tactics leave, back into `mkR` form *)
Ltac fold_mkR :=
  match goal with
  | |- context [TNode
      (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
         (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
      None
      (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
         (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))] =>
      change (TNode
      (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty)))
         (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty))))
      None
      (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2)
         (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
      with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  end.

(* the contract's Post, word for word (lib/Prog/reac_served_unmark_all_c.v) *)
Definition um_post (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  (arg regs 0 = 0 -> m' = m)
  /\ (arg regs 0 <> 0 -> forall kbs tab gbs,
        nlk_at m kbs -> iftab_at m kbs tab -> marks_at m (arg regs 0) gbs ->
        let U := unmark tab (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
        (exists gbs', marks_at m' (arg regs 0) gbs' /\ marks_wf gbs' /\ mk_n gbs' = 0)
        /\ (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
              /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
              /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m' kbs' tab
              /\ nk_next kbs' = Z.of_nat (k_next (snd U))
              /\ nk_sent kbs' = fst U /\ nk_n_sent kbs' = Z.of_nat (length (fst U))
              /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
              /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
              /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2 * MARKS_MAX)).

(* ==========================================================================
   2. The walk, for a non-NULL marks block
   ========================================================================== *)

(* the two library contracts' Posts, read out of their text *)
Definition rd_post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(lazymatch eval cbv delta [reac_link_alias_read_contract] in reac_link_alias_read_contract with
        | leaf _ _ _ _ ?Q => exact Q end).
Definition wr_post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(lazymatch eval cbv delta [reac_link_alias_write_contract] in reac_link_alias_write_contract with
        | leaf _ _ _ _ ?Q => exact Q end).

Lemma rd_post_ext : post_ext rd_post.
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H. unfold rd_post in *. intros kbs tab nm Hk Ht Hs.
  unfold arg in *. rewrite <- E2. rewrite <- !E1.
  apply H; [exact Hk | exact Ht |]. rewrite E1. exact Hs.
Qed.

Lemma wr_post_ext : post_ext wr_post.
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H. unfold wr_post in *. intros kbs tab nm al Hk Ht Hs Ha.
  unfold arg in *. rewrite <- E2.
  apply H; [exact Hk | exact Ht | rewrite E1; exact Hs | rewrite E1; exact Ha].
Qed.

Section Walk.
Variable HRD : reac_link_alias_read_contract.
Variable HWR : reac_link_alias_write_contract.
Variable HB : bcmp_contract.
Variable HMS : memset_contract.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Variables (kbs0 : list byte) (tab : list (list byte * Z)) (gbs : list byte).

Hypothesis HNZ : bv_unsigned a0 <> 0.
Hypothesis HKN : nlk_at m kbs0.
Hypothesis HFG : apart_gnl (bv_unsigned sp - 17232) 17232.
Hypothesis HWF0 : nlk_wf kbs0.
Hypothesis HOP0 : nk_open kbs0 = 0.
Hypothesis HOB : nk_opened kbs0 + 2 * MARKS_MAX < 2 ^ 31.
Hypothesis HCB : nk_closed kbs0 + 2 * MARKS_MAX < 2 ^ 31.
Hypothesis HIT0 : iftab_at m kbs0 tab.
Hypothesis HEF : bv_unsigned tp + ERRNO_TP_OFF + 4 <= bv_unsigned sp - 17232
                 \/ bv_unsigned sp <= bv_unsigned tp + ERRNO_TP_OFF.
Hypothesis HEG : apart_gnl (bv_unsigned tp + ERRNO_TP_OFF) 4.
Hypothesis HTB : forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  (p + (Z.of_nat (length n2) + 1) <= bv_unsigned sp - 17232 \/ bv_unsigned sp <= p)
  /\ apart_gnl p (Z.of_nat (length n2) + 1)
  /\ apart (bv_unsigned tp + ERRNO_TP_OFF) 4 p (Z.of_nat (length n2) + 1)
  /\ apart (bv_unsigned a0) MK_SIZE p (Z.of_nat (length n2) + 1).
Hypothesis HAF : bv_unsigned a0 + MK_SIZE <= bv_unsigned sp - 17232 \/ bv_unsigned sp <= bv_unsigned a0.
Hypothesis HAE : apart (bv_unsigned tp + ERRNO_TP_OFF) 4 (bv_unsigned a0) MK_SIZE.
Hypothesis HAG : apart_gnl (bv_unsigned a0) MK_SIZE.
Hypothesis HMK0 : marks_at m (bv_unsigned a0) gbs.
Hypothesis HMW : marks_wf gbs.
Hypothesis HLO : lo + 17232 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp < 2 ^ 63.
Hypothesis HL0 : 0 <= lo.
Hypothesis HEMP : A_EMPTY < lo \/ bv_unsigned sp <= A_EMPTY.

Local Abbreviation SPV := (Z_to_bv 64 (bv_unsigned sp + -304)).
Local Abbreviation S1V c := (Z_to_bv 64 (bv_unsigned a0 + 4 + 16 * Z.of_nat c)).
Local Abbreviation S4V c := (Z_to_bv 64 (Z.of_nat c)).
Local Abbreviation S2V := (Z_to_bv 64 66369).
Local Abbreviation S3V := (Z_to_bv 64 66408).
Local Abbreviation NN := (Z.to_nat (mk_n gbs)).
Local Abbreviation NAMES := (mk_names gbs).

Lemma HLG : length gbs = 516%nat.
Proof. destruct HMK0 as [_ L]. unfold MK_SIZE in L. lia. Qed.

Lemma HAR : 0 <= bv_unsigned a0 /\ bv_unsigned a0 + 516 <= 2 ^ 64.
Proof. destruct HMK0 as [U L]. pose proof (u8arr_bound rsegs _ _ _ U) as B. unfold MK_SIZE in L. lia. Qed.

Lemma HNR : 0 <= mk_n gbs <= 32.
Proof. exact (marks_n_range gbs HMW). Qed.

Definition R0 : bvmap 5 word :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition W0 : list ivl :=
  [(bv_unsigned sp - 17232, bv_unsigned sp); (A_G_NL, A_G_NL + NK_N_SENT + 4);
   (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4);
   (bv_unsigned a0, bv_unsigned a0 + MK_SIZE)].

Definition QQ : machine_state -> Prop :=
  fun ms' => exists (regs' : bvmap 5 word) (m' : word -> option byte),
    ms' = MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    regs_preserved R0 regs' /\ munch W0 m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\ um_post R0 m regs' m'.

Lemma QQ_ext : q_ext QQ.
Proof. unfold QQ, W0. apply leaf_q_ext. intros q1 q2 m' _ H. exact H. Qed.

(* the memory the loop keeps: the marks block, errno, the frame (alias buffer, then the six saved
   words), the stack below it, and the write set so far *)
Definition minv (mi : word -> option byte) : Prop :=
  u8arr rsegs mi (bv_unsigned a0) gbs /\ wr_at rsegs mi (bv_unsigned tp + ERRNO_TP_OFF) 4
  /\ (exists junk, rw_cells rsegs mi (bv_unsigned sp + -304)
                     [CB 256 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
  /\ stk rsegs mi lo (bv_unsigned sp + -304)
  /\ munch W0 m mi /\ wmono rsegs m mi /\ mem_inv rsegs mi.

(* the fake kernel at the loop head, `c` names done *)
Definition kinv (mi : word -> option byte) (kbs : list byte) (c : nat) : Prop :=
  nlk_at mi kbs /\ nlk_wf kbs /\ iftab_at mi kbs tab
  /\ nk_chunks kbs = nk_chunks kbs0 /\ nk_end_errno kbs = nk_end_errno kbs0 /\ nk_n_if kbs = nk_n_if kbs0
  /\ unmark_walk tab (skipn c NAMES) (nk_sent kbs) (nk_kstate kbs)
     = unmark tab NAMES (nk_sent kbs0) (nk_kstate kbs0)
  /\ nk_open kbs = 0 /\ nk_misuse kbs = nk_misuse kbs0
  /\ nk_opened kbs - nk_closed kbs = nk_opened kbs0 - nk_closed kbs0
  /\ nk_opened kbs0 <= nk_opened kbs <= nk_opened kbs0 + 2 * Z.of_nat c.

Definition inv (mi : word -> option byte) (kbs : list byte) (c : nat) : Prop := kinv mi kbs c /\ minv mi.

(* an if_name slot read in a later memory is the slot the Pre read *)
Lemma tab_back : forall mi i p, munch W0 m mi -> (i < 80)%nat ->
  u64_at mi (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p.
Proof.
  intros mi i p MU Hi U. unfold u64_at in *. apply (bytes_at_back W0 m mi _ _ U MU). rewrite length_le8.
  unfold W0. cbn [disjoint_from]. unfold apart_gnl in *.
  unfold NK_IF_NAME, NK_N_SENT, NK_SIZE, MK_SIZE, A_G_NL in *. lia.
Qed.

Lemma tab_ok : forall mi kbs i n2 ix p, munch W0 m mi -> iftab_at mi kbs tab ->
  nth_error tab i = Some (n2, ix) -> u64_at mi (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  (p + (Z.of_nat (length n2) + 1) <= bv_unsigned sp - 17232 \/ bv_unsigned sp <= p)
  /\ apart_gnl p (Z.of_nat (length n2) + 1)
  /\ apart (bv_unsigned tp + ERRNO_TP_OFF) 4 p (Z.of_nat (length n2) + 1)
  /\ apart (bv_unsigned a0) MK_SIZE p (Z.of_nat (length n2) + 1).
Proof.
  intros mi kbs i n2 ix p MU (_ & Hl & _) E U.
  assert (Hi : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  apply (HTB i n2 ix p E). apply (tab_back mi i p MU); [lia | exact U].
Qed.

(* ---- the tail: memset(m, 0, 516), the epilogue and the return ---- *)
Lemma tail_ok : forall (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 : word)
    mi kbs, inv mi kbs NN ->
  evt rsegs QQ (MS (mkR xra SPV gp tp xt0 xt1 xt2 a0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4
                        s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                   F (Z_to_bv 64 0x16800) fc None mi (seg_rom rsegs)).
Proof.
  intros xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 mi kbs
    ((NL & WF & IT & CH & EE & NI & UW & OP & MSU & OC & OB) & (MK & ER & (junk & FR) & ST & MU & WM & MI)).
  pose proof HLG as LG. pose proof HAR as AR. pose proof HNR as NR.
  zstep. zstep. zstep. zstep.
  fold_mkR.
  assert (RW : rw_cells rsegs mi (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 516))) gbs]).
  { rewrite unsigned_lit by lia. change (Z.to_nat 516) with 516%nat. rewrite <- LG.
    apply rw_cells_of_u8arr. exact MK. }
  eapply evt_cut; [eapply HMS; [exact RW | exact MI]|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
              & -> & MU1 & WM1 & MI1 & RW1).
  rewrite ret_pc_even by (lia || reflexivity).
  rewrite !unsigned_lit in MU1, RW1 by lia.
  change (Z.to_nat 516) with 516%nat in RW1. change (0 mod 256) with 0 in RW1.
  assert (D1 : disjoint_from [(bv_unsigned a0, bv_unsigned a0 + 516)] (bv_unsigned sp + -304)
                 (Z.of_nat (cells_size [CB 256 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))).
  { cbn [disjoint_from cells_size csize Nat.add]. unfold MK_SIZE in HAF. lia. }
  pose proof (rw_cells_transport rsegs _ mi m1 _ _ FR MU1 WM1 D1) as FR1.
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp + -304)).
  { apply (stk_transport_rw _ mi m1 lo _ _ _ ST MU1 WM1 RW1). intros x Hx.
    cbn [outside cells_size csize Nat.add]. lia. }
  assert (NL1 : nlk_at m1 kbs).
  { destruct NL as [U L]. split; [|exact L]. apply (u8arr_transport rsegs _ mi m1 _ _ U MU1 WM1).
    rewrite L. cbn [disjoint_from]. unfold apart_gnl, MK_SIZE in HAG. lia. }
  assert (IT1 : iftab_at m1 kbs tab).
  { apply (iftab_transport _ mi m1 kbs tab IT MU1).
    - cbn [disjoint_from]. unfold apart_gnl, MK_SIZE, NK_IF_NAME, NK_SIZE in *. lia.
    - cbn [disjoint_from]. unfold apart_gnl, MK_SIZE, NK_IF_INDEX, NK_SIZE in *. lia.
    - intros i n2 ix p E U. destruct (tab_ok mi kbs i n2 ix p MU IT E U) as (_ & _ & _ & Ap).
      cbn [disjoint_from]. unfold apart, MK_SIZE in Ap. lia. }
  pose proof (u8arr_of_rw_cells rsegs _ _ _ _ RW1) as MK1.
  assert (MU2 : munch W0 m m1).
  { apply (munch_trans W0 m mi m1 MU).
    apply (munch_weaken [(bv_unsigned a0, bv_unsigned a0 + 516)] W0 mi m1); [|exact MU1].
    unfold sub_fp, W0, MK_SIZE. cbn [outside]. intros x Hx. lia. }
  pose proof (wmono_trans rsegs m mi m1 WM WM1) as WM2.
  clear RW FR ST MU WM MI MK MU1 WM1 D1 NL IT.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR1 ST1 (bv_unsigned sp).
  apply evt_done. unfold QQ. fold_mkR. eexists; eexists. split; [reflexivity|].
  split; [unfold R0; apply regs_preserved_mkR|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact MI1|]. split; [exact ST1|].
  unfold um_post, R0. rewrite mkR_a0. split; [intros H; exfalso; exact (HNZ H)|].
  intros _ kbs1 tab1 gbs1 HK1 HT1 HG1.
  pose proof (nlk_unique m _ _ HK1 HKN) as ->.
  pose proof (iftab_unique m kbs0 _ _ HT1 HIT0) as ->.
  pose proof (marks_unique m _ _ _ HG1 HMK0) as ->.
  cbv zeta.
  assert (Z0 : mk_n (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) 516) = 0)
    by (vm_compute; reflexivity).
  split.
  - eexists. split; [split; [exact MK1 | rewrite repeat_length; reflexivity]|].
    split; [split; [rewrite Z0; unfold MARKS_MAX; lia | intros i Hi; rewrite Z0 in Hi; lia] | exact Z0].
  - rewrite skipn_all2 in UW by (rewrite mk_names_length; lia).
    cbn [unmark_walk] in UW. rewrite <- UW. cbn [fst snd].
    pose proof WF as (_ & Wn & Ws & _).
    exists kbs. split; [exact NL1|]. split; [exact WF|]. split; [exact CH|]. split; [exact EE|].
    split; [exact NI|]. split; [exact IT1|].
    split; [unfold nk_kstate; cbn [k_next]; rewrite Z2Nat.id by lia; reflexivity|].
    split; [reflexivity|].
    split; [unfold nk_sent; rewrite length_map, length_seq, Z2Nat.id by lia; reflexivity|].
    split; [exact OP|]. split; [exact MSU|]. split; [exact OC|]. unfold MARKS_MAX. lia.
Qed.

(* the loop head 0x167b4 and the join 0x167f0, `c` the round *)
Definition HEAD (c : nat) : Prop :=
  forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) mi kbs, inv mi kbs c ->
  evt rsegs QQ (MS (mkR xra SPV gp tp xt0 xt1 xt2 a0 (S1V c) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 S2V S3V (S4V c)
                        s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                   F (Z_to_bv 64 0x167b4) fc None mi (seg_rom rsegs)).

Definition JOINP (c : nat) : Prop :=
  forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) mi kbs, inv mi kbs (S c) ->
  evt rsegs QQ (MS (mkR xra SPV gp tp xt0 xt1 xt2 a0 (S1V c) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 S2V S3V (S4V c)
                        s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                   F (Z_to_bv 64 0x167f0) fc None mi (seg_rom rsegs)).

Lemma n_load : sext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (skipn 0 gbs)))) = Z_to_bv 64 (mk_n gbs).
Proof.
  pose proof HLG as LG. pose proof HNR as NR.
  rewrite lw_val; [reflexivity | rewrite length_firstn, length_skipn, LG; reflexivity |].
  change (bytes_le_to_Z (firstn 4 (skipn 0 gbs))) with (mk_n gbs). lia.
Qed.

Lemma n_read : forall mi, u8arr rsegs mi (bv_unsigned a0) gbs ->
  ov_read_bytes rsegs mi a0 4 = Some (firstn 4 (skipn 0 gbs)).
Proof.
  intros mi MK. pose proof HLG as LG.
  pose proof (bytes_at_ov_read rsegs _ _ gbs 0 4 (proj1 MK) ltac:(lia)) as HR.
  cbn [Z.of_nat] in HR. rewrite Z.add_0_r in HR. unfold wa in HR. rewrite Z_to_bv_bv_unsigned in HR. exact HR.
Qed.

Lemma join_ok : forall c, (c < NN)%nat -> ((S c < NN)%nat -> HEAD (S c)) -> JOINP c.
Proof.
  intros c Hc HH xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mi kbs I.
  pose proof I as (_ & (MK & _)).
  pose proof HLG as LG. pose proof HAR as AR. pose proof HNR as NR.
  pose proof (n_read mi MK) as HR.
  zstep. rewrite n_load.
  zstep. zstep. zstep.
  rewrite lts_small by lia.
  destruct (Nat.lt_ge_cases (S c) NN) as [Hlt|Hge].
  - replace (Z.of_nat c + 1 <? mk_n gbs) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
    fold_mkR.
    replace (Z_to_bv 64 (Z.of_nat c + 1)) with (S4V (S c)) by (f_equal; lia).
    replace (Z_to_bv 64 (bv_unsigned a0 + 4 + 16 * Z.of_nat c + 16)) with (S1V (S c)) by (f_equal; lia).
    exact (HH Hlt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mi kbs I).
  - replace (Z.of_nat c + 1 <? mk_n gbs) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    fold_mkR.
    assert (E : S c = NN) by lia. rewrite E in I.
    exact (tail_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mi kbs I).
Qed.

(* ---- the frame: the alias buffer, then the six saved words ---- *)

Lemma frame_split : forall mi j,
  rw_cells rsegs mi (bv_unsigned sp + -304) [CB 256 j; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs mi (bv_unsigned sp + -304) [CB 256 j]
  /\ rw_cells rsegs mi (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Proof.
  intros mi j H.
  pose proof (proj1 (rw_cells_app_iff mi _ [CB 256 j] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) H) as [H1 H2].
  split; [exact H1|].
  assert (E : bv_unsigned sp + -304 + Z.of_nat (cells_size [CB 256 j]) = bv_unsigned sp + -48) by (cbn; lia).
  rewrite E in H2. exact H2.
Qed.

Lemma frame_join : forall mi j,
  rw_cells rsegs mi (bv_unsigned sp + -304) [CB 256 j] ->
  rw_cells rsegs mi (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs mi (bv_unsigned sp + -304) [CB 256 j; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Proof.
  intros mi j H1 H2.
  apply (proj2 (rw_cells_app_iff mi _ [CB 256 j] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  split; [exact H1|].
  assert (E : bv_unsigned sp + -304 + Z.of_nat (cells_size [CB 256 j]) = bv_unsigned sp + -48) by (cbn; lia).
  rewrite E. exact H2.
Qed.

(* the loop's memory after a callee whose write set misses the marks block and the saved words *)
Lemma minv_after : forall W mi m1, minv mi -> munch W mi m1 -> wmono rsegs mi m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -304) -> sub_fp W W0 ->
  disjoint_from W (bv_unsigned a0) 516 -> disjoint_from W (bv_unsigned sp + -48) 48 ->
  (exists junk, rw_cells rsegs m1 (bv_unsigned sp + -304) [CB 256 junk]) -> minv m1.
Proof.
  intros W mi m1 (MK & ER & (junk & FR) & _ & MU & WM & _) MU1 WM1 MI1 ST1 SB D1 D2 (j1 & B1).
  destruct (frame_split mi junk FR) as [_ SV].
  pose proof HLG as LG.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply (u8arr_transport rsegs W mi m1 _ _ MK MU1 WM1). rewrite LG. exact D1.
  - exact (wr_at_transport rsegs mi m1 _ _ ER WM1).
  - exists j1. apply (frame_join m1 j1 B1). exact (rw_cells_transport rsegs W mi m1 _ _ SV MU1 WM1 D2).
  - exact ST1.
  - exact (munch_trans W0 m mi m1 MU (munch_weaken W W0 mi m1 SB MU1)).
  - exact (wmono_trans rsegs m mi m1 WM WM1).
  - exact MI1.
Qed.

Lemma USP : bv_unsigned SPV = bv_unsigned sp + -304.
Proof. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma US1 : forall c, (c < NN)%nat -> bv_unsigned (S1V c) = bv_unsigned a0 + 4 + 16 * Z.of_nat c.
Proof. intros c Hc. pose proof HAR. pose proof HNR. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma nm_len : forall c, (c < NN)%nat -> (length (cstr (slice gbs (4 + 16 * Z.of_nat c) 16)) <= 15)%nat.
Proof.
  intros c Hc. pose proof HMW as [_ T]. pose proof HNR.
  specialize (T (Z.of_nat c) ltac:(lia)). unfold MK_NAME, MARK_LEN in T.
  unfold cstr. rewrite length_firstn. lia.
Qed.

Lemma name_at : forall c mi, (c < NN)%nat -> u8arr rsegs mi (bv_unsigned a0) gbs ->
  cstr_at mi (bv_unsigned a0 + 4 + 16 * Z.of_nat c) (cstr (slice gbs (4 + 16 * Z.of_nat c) 16)).
Proof.
  intros c mi Hc MK. pose proof HLG as LG. pose proof HNR.
  destruct (slot_cstr mi (bv_unsigned a0) gbs (Z.of_nat c) (proj1 MK) ltac:(rewrite LG; reflexivity) HMW
              ltac:(lia)) as [B N].
  split; [|exact N].
  replace (bv_unsigned a0 + 4 + 16 * Z.of_nat c) with (bv_unsigned a0 + (4 + 16 * Z.of_nat c)) by lia. exact B.
Qed.

Ltac regs_z :=
  rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_errno.

(* ---- one round: alias_read, bcmp, alias_write ---- *)
Lemma body_ok : forall c, (c < NN)%nat -> JOINP c -> HEAD c.
Proof.
  intros c Hc HJ xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mi kbs I. unfold JOINP in HJ.
  pose proof I as ((NL & WF & IT & CH & EE & NI & UW & OP & MSU & OC & OB) & MI0).
  pose proof MI0 as (MK & ER & (junk & FR) & ST & MU & WM & MI).
  pose proof HLG as LG. pose proof HAR as AR. pose proof HNR as NR.
  pose proof USP as Usp. pose proof (US1 c Hc) as Us1. pose proof (nm_len c Hc) as Ln.
  pose proof (mk_names_nth gbs c Hc) as Enm. pose proof (name_at c mi Hc MK) as NMA.
  set (nm := cstr (slice gbs (4 + 16 * Z.of_nat c) 16)) in *.
  destruct (frame_split mi junk FR) as [BUF SV].
  pose proof (WF) as (_ & _ & _ & _ & _ & _ & _ & _ & We & Wso & Wse & _).
  assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  assert (U256 : bv_unsigned (Z_to_bv 64 256) = 256) by reflexivity.
  unfold apart_gnl, apart, MARKS_MAX, MK_SIZE in *.
  zstep. zstep. zstep. zstep. zstep. zstep.
  fold_mkR.
  (* reac_link_alias_read(name, NULL, 0, sp, 256) at 0x167c8 *)
  eapply (leaf_call _ _ _ _ _ HRD rd_post_ext QQ QQ_ext) with (F := F) (fc := fc) (m := mi) (lo := lo).
  { hnf. exists kbs, tab, (Some nm).
    unfold frame_apart_gnl, apart_frame, buf_arg, apart_gnl, apart.
    regs_z. rewrite ?Usp, ?Us1, ?U0, ?U256.
    split; [exact NL|]. split; [lia|]. split; [exact WF|]. split; [exact OP|]. split; [lia|]. split; [lia|].
    split; [exact IT|]. split; [exact ER|]. split; [lia|]. split; [lia|].
    split; [split; [lia | exact NMA]|].
    split; [intros H; exfalso; apply H; reflexivity|].
    split; [intros _ _; exists junk; exact BUF|].
    split.
    { intros i n2 ix p E U. destruct (tab_ok mi kbs i n2 ix p MU IT E U) as (Fp & Gp & Ep & Ap).
      unfold apart_gnl, apart, MK_SIZE in Fp, Gp, Ep, Ap. repeat split; intros; lia. }
    split; [intros s Es; injection Es as <-; split; intros; lia|].
    split; [intros H; exfalso; apply H; reflexivity|].
    split; [intros H; exfalso; apply H; reflexivity|].
    split; [intros _; lia|].
    split; [intros s Es; injection Es as <-; split; lia|].
    split; [intros H; exfalso; apply H; reflexivity|].
    intros _; split; lia. }
  { exact MI. }
  { rewrite Usp. exact ST. }
  { rewrite Usp. lia. }
  { rewrite Usp. lia. }
  intros ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 m1 MU1 WM1 MI1 ST1 PO.
  specialize (PO kbs tab (Some nm) NL IT ltac:(regs_z; rewrite Us1; split; [lia | exact NMA])).
  cbv zeta in PO.
  match type of PO with context [read_lib ?t ?n ?k ?a ?r ?K] => set (R := read_lib t n k a r K) in PO end.
  assert (HRe : R = read_core tab (Some nm) 0 ALIAS_MAX (nk_sent kbs) (nk_kstate kbs)) by reflexivity.
  destruct PO as (Hrc & (kbs1 & NL1 & WF1 & CH1 & EE1 & NI1 & IT1 & NX1 & SO1 & SE1 & SN1 & NS1 & OP1 & MS1
                         & OC1 & OB1 & OZ1) & _ & AL1 & _ & BF1).
  assert (Ea : a01 = wz (r_rc R)) by exact Hrc. subst a01.
  rewrite ?mkR_a3, ?mkR_a4 in AL1, BF1. rewrite ?Usp, ?U256 in AL1, BF1.
  cbv beta in MU1. rewrite ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_errno in MU1.
  rewrite ?Usp, ?U0, ?U256 in MU1. rewrite Usp in ST1.
  replace (bv_unsigned sp + -304 =? 0) with false in MU1 by (symmetry; apply Z.eqb_neq; lia).
  cbn [Z.eqb] in MU1.
  specialize (AL1 ltac:(lia) ltac:(lia)). destruct (BF1 ltac:(lia) ltac:(lia)) as (j1 & B1).
  change (Z.to_nat 256) with 256%nat in B1.
  assert (MI1' : minv m1).
  { apply (minv_after _ mi m1 MI0 MU1 WM1 MI1 ST1).
    - unfold sub_fp, W0. cbn [outside]. intros x Hx. unfold MK_SIZE. lia.
    - cbn [disjoint_from]. unfold NK_N_SENT, NK_SIZE, A_G_NL in *. lia.
    - cbn [disjoint_from]. unfold NK_N_SENT, NK_SIZE, A_G_NL in *. lia.
    - exists j1. exact B1. }
  assert (KS1 : nk_kstate kbs1 = r_state R).
  { destruct (read_state_ce tab (Some nm) 0 ALIAS_MAX (nk_sent kbs) (nk_kstate kbs)) as [C1 E1].
    rewrite <- HRe in C1, E1.
    apply nk_kstate_eq; [rewrite CH1, C1; reflexivity | exact NX1 | rewrite EE1, E1; reflexivity
                         | exact SO1 | exact SE1]. }
  assert (RR : - 2 ^ 32 < r_rc R < 2 ^ 32).
  { rewrite HRe. apply read_rc_range; unfold nk_kstate; cbn [k_sock k_send k_end]; lia. }
  rewrite (skipn_nth NAMES c nm Enm) in UW. cbn [unmark_walk] in UW. rewrite <- HRe in UW.
  assert (INV1 : unmark_walk tab (skipn (S c) NAMES) (r_reqs R) (r_state R)
                 = unmark tab NAMES (nk_sent kbs0) (nk_kstate kbs0) -> inv m1 kbs1 (S c)).
  { intros UW1. split; [|exact MI1'].
    split; [exact NL1|]. split; [exact WF1|]. split; [exact IT1|].
    split; [rewrite CH1; exact CH|]. split; [rewrite EE1; exact EE|]. split; [rewrite NI1; exact NI|].
    split; [rewrite SN1, KS1; exact UW1|].
    split; [exact OP1|]. split; [rewrite MS1; exact MSU|]. split; [lia|]. lia. }
  rewrite ret_pc_even by (lia || reflexivity).
  zstep.
  unfold wz. rewrite bv_eqb_z0 by lia.
  destruct (Z.eqb_spec (r_rc R) 0) as [R0|R0].
  2:{ cbn [negb]. fold_mkR. eapply HJ. apply INV1.
      replace (r_rc R =? 0) with false in UW by (symmetry; apply Z.eqb_neq; exact R0).
      cbn [negb] in UW. exact UW. }
  cbn [negb].
  replace (r_rc R =? 0) with true in UW by (symmetry; apply Z.eqb_eq; exact R0). cbn [negb] in UW.
  (* bcmp(sp, "reac-pw:served", 15) at 0x167dc *)
  zstep. zstep. zstep. zstep.
  fold_mkR.
  destruct (bcmp_served (r_alias R) (proj2 AL1)) as (v & Hv & Rv & Iv).
  eapply evt_cut.
  { eapply HB with (ls := r_alias R ++ [zb 0]) (rs := S_SERVED ++ [zb 0]) (v := v).
    - rewrite Usp. exact (proj1 AL1).
    - rewrite unsigned_lit by lia. exact (served_at m1 MI1).
    - rewrite unsigned_lit by lia. exact Hv.
    - exact MI1. }
  intros ms' (t02 & t12 & t22 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & m2
              & -> & MU2 & WM2 & MI2 & _ & _).
  assert (Em : m2 = m1) by (apply functional_extensionality; intros x; exact (MU2 x Logic.I)). subst m2.
  rewrite ret_pc_even by (lia || reflexivity).
  zstep. rewrite bv_eqb_z0 by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0].
  2:{ cbn [negb]. fold_mkR. eapply HJ. apply INV1.
      destruct (bl_eqb (r_alias R) S_SERVED) eqn:BS; [exfalso; apply V0, Iv; reflexivity|].
      cbn [negb] in UW. exact UW. }
  cbn [negb].
  pose proof (proj1 Iv V0) as BS. rewrite BS in UW. cbn [negb] in UW.
  (* reac_link_alias_write(name, "") at 0x167ec *)
  zstep. zstep. zstep.
  fold_mkR.
  pose proof MI1' as (MK1 & ER1 & (jf1 & FR1) & _ & MUw & _ & _).
  pose proof (name_at c m1 Hc MK1) as NMA1. change (cstr (slice gbs (4 + 16 * Z.of_nat c) 16)) with nm in NMA1.
  assert (U3 : bv_unsigned S3V = 66408) by reflexivity.
  unfold A_EMPTY in *.
  eapply (leaf_call _ _ _ _ _ HWR wr_post_ext QQ QQ_ext) with (F := F) (fc := fc) (m := m1) (lo := lo).
  { hnf. exists kbs1, tab, (Some nm), (Some []).
    unfold frame_apart_gnl, apart_frame, apart_gnl, apart.
    regs_z. rewrite ?Usp, ?Us1, ?U3.
    split; [exact NL1|]. split; [lia|]. split; [exact WF1|]. split; [exact OP1|]. split; [lia|]. split; [lia|].
    split; [exact IT1|]. split; [exact ER1|]. split; [lia|]. split; [lia|].
    split; [split; [lia | exact NMA1]|].
    split; [split; [lia | split; [exact (empty_at m1 MI1) | intros []]]|].
    split.
    { intros i n2 ix p E U. destruct (tab_ok m1 kbs1 i n2 ix p MUw IT1 E U) as (Fp & Gp & Ep & Ap).
      unfold apart_gnl, apart, MK_SIZE in Fp, Gp, Ep, Ap. repeat split; lia. }
    split; [intros s Es; injection Es as <-; split; lia|].
    split; [intros s Es; injection Es as <-; cbn [length Z.of_nat]; unfold A_G_NL; split; lia|].
    intros s Es; injection Es as <-. exists (map (Z_to_bv 8) [46; 0; 117; 115; 97; 103; 101]).
    split; [exact (empty_slack m1 MI1) | vm_compute; intros H; discriminate]. }
  { exact MI1. }
  { rewrite Usp. exact ST1. }
  { rewrite Usp. lia. }
  { rewrite Usp. lia. }
  intros ra3 t03 t13 t23 a03 a13 a23 a33 a43 a53 a63 a73 t33 t43 t53 t63 m3 MU3 WM3 MI3 ST3 PO3.
  specialize (PO3 kbs1 tab (Some nm) (Some []) NL1 IT1
                ltac:(regs_z; rewrite Us1; split; [lia | exact NMA1])
                ltac:(regs_z; rewrite U3; split; [lia | split; [exact (empty_at m1 MI1) | intros []]])).
  cbv zeta in PO3.
  destruct PO3 as (_ & (kbs2 & NL2 & WF2 & CH2 & EE2 & NI2 & IT2 & NX2 & SO2 & SE2 & SN2 & NS2 & OP2 & MS2
                         & OC2 & OB2 & OZ2)).
  set (Wm := write_lib tab (Some nm) (Some []) (nk_sent kbs1) (nk_kstate kbs1)) in *.
  assert (HWe : Wm = write_core tab (Some nm) (Some []) (r_reqs R) (r_state R)).
  { unfold Wm, write_lib. rewrite SN1, KS1. reflexivity. }
  assert (KS2 : nk_kstate kbs2 = w_state Wm).
  { destruct (write_state_ce tab (Some nm) (Some []) (nk_sent kbs1) (nk_kstate kbs1)) as [C2 E2].
    change (write_core tab (Some nm) (Some []) (nk_sent kbs1) (nk_kstate kbs1)) with Wm in C2, E2.
    apply nk_kstate_eq; [rewrite CH2, C2; reflexivity | exact NX2 | rewrite EE2, E2; reflexivity
                         | exact SO2 | exact SE2]. }
  cbv beta in MU3. rewrite ?mkR_errno in MU3. rewrite Usp in ST3, MU3.
  rewrite ret_pc_even by (lia || reflexivity).
  assert (MI3' : minv m3).
  { destruct (frame_split m1 jf1 FR1) as [BUF1 _].
    apply (minv_after _ m1 m3 MI1' MU3 WM3 MI3 ST3).
    - unfold sub_fp, W0. cbn [outside]. intros x Hx. unfold MK_SIZE. lia.
    - cbn [disjoint_from]. unfold NK_N_SENT, NK_SIZE in *. lia.
    - cbn [disjoint_from]. unfold NK_N_SENT, NK_SIZE in *. lia.
    - exists jf1. apply (rw_cells_transport rsegs _ m1 m3 _ _ BUF1 MU3 WM3).
      cbn [disjoint_from cells_size csize Nat.add]. unfold NK_N_SENT, NK_SIZE in *. lia. }
  eapply HJ.
  split; [|exact MI3'].
  split; [exact NL2|]. split; [exact WF2|]. split; [exact IT2|].
  split; [rewrite CH2, CH1; exact CH|]. split; [rewrite EE2, EE1; exact EE|].
  split; [rewrite NI2, NI1; exact NI|].
  split; [rewrite SN2, KS2, HWe; exact UW|].
  split; [exact OP2|]. split; [rewrite MS2, MS1; exact MSU|]. split; [lia|]. lia.
Qed.

Lemma head_all : forall k c, (c + k = NN)%nat -> (c < NN)%nat -> HEAD c.
Proof.
  induction k as [|k IH]; intros c E Hc; [lia|].
  apply body_ok; [exact Hc|]. apply join_ok; [exact Hc|]. intros Hlt. apply IH; lia.
Qed.

(* ---- the entry: the frame push, the load of n and the loop setup ---- *)
Lemma entry_ok : stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  wr_at rsegs m (bv_unsigned tp + ERRNO_TP_OFF) 4 ->
  evt rsegs QQ (MS R0 F (Z_to_bv 64 0x16770) fc None m (seg_rom rsegs)).
Proof.
  intros ST MI ER. unfold R0.
  pose proof HLG as LG. pose proof HAR as AR. pose proof HNR as NR.
  pose proof HMK0 as [MK _]. pose proof HKN as NL0. pose proof HIT0 as IT0.
  unfold MK_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp + -304, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 304%nat ST.
  zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (INV0 : inv m1 kbs0 0).
  { split.
    - split; [|split; [exact HWF0|split]].
      + destruct NL0 as [U L]. split; [|exact L]. apply (u8arr_transport rsegs _ m m1 _ _ U MU WM).
        rewrite L. cbn [disjoint_from]. unfold apart_gnl in HFG. lia.
      + apply (iftab_transport _ m m1 kbs0 tab IT0 MU).
        * cbn [disjoint_from]. unfold apart_gnl, NK_IF_NAME, NK_SIZE in *. lia.
        * cbn [disjoint_from]. unfold apart_gnl, NK_IF_INDEX, NK_SIZE in *. lia.
        * intros i n2 ix p E U. destruct (HTB i n2 ix p E U) as (Fp & _). cbn [disjoint_from]. lia.
      + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [exact HOP0|]. split; [reflexivity|]. split; [reflexivity|]. lia.
    - split; [exact MK|]. split; [exact ER|]. split; [eexists; exact FR|]. split; [exact ST|].
      split; [|split; [exact WM | exact MI]].
      apply (munch_weaken [(bv_unsigned sp + -304, bv_unsigned sp)] W0 m m1); [|exact MU].
      unfold sub_fp, W0. cbn [outside]. intros x Hx. lia. }
  pose proof (n_read _ MK) as HR.
  zstep. rewrite n_load.
  zstep.
  rewrite lts_small by lia.
  destruct (Z.ltb_spec 0 (mk_n gbs)) as [Hpos|Hz].
  - cbn [negb].
    zstep. zstep. zstep. zstep. zstep. zstep.
    fold_mkR.
    replace (Z_to_bv 64 (bv_unsigned a0 + 4)) with (S1V 0) by (f_equal; lia).
    pose proof (head_all NN 0%nat ltac:(lia) ltac:(lia)) as H0. unfold HEAD in H0.
    exact (H0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 kbs0 INV0).
  - cbn [negb]. fold_mkR.
    assert (E0 : NN = 0%nat) by lia. rewrite <- E0 in INV0.
    exact (tail_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 kbs0 INV0).
Qed.

End Walk.

(* ==========================================================================
   3. The contract
   ========================================================================== *)

Theorem reac_served_unmark_all_holds :
  reac_link_alias_read_contract -> reac_link_alias_write_contract -> bcmp_contract -> memset_contract ->
  reac_served_unmark_all_contract.
Proof.
  intros HRD HWR HB HMS. unfold reac_served_unmark_all_contract. apply leaf_intro.
  - intros r1 r2 m E H. cbv beta in H |- *.
    unfold frame_apart_gnl, apart_frame, errno_at, arg, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m E. cbv beta. unfold errno_at, arg. rewrite !E. reflexivity.
  - intros r1 r2 m q1 q2 m' E1 E2 H. cbv beta in H |- *. unfold arg in *. rewrite <- !E1. exact H.
  - unfold leaf_walk, REAC_SERVED_UNMARK_ALL.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros (kbs & tab & NL & FG & WF & OP & OB & CB & IT & ER & EF & EG & TB & HA) MI ST LO SP.
    assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
    cbv beta.
    unfold frame_apart_gnl, apart_frame in *. rewrite ?mkR_sp, ?mkR_errno, ?mkR_a0 in *.
    destruct (Z.eq_dec (bv_unsigned a0) 0) as [Z0|NZ].
    + (* a0 = NULL: `beqz a0` to the `ret`, no frame *)
      zstep. if_true. zstep.
      apply evt_done. eexists; eexists. split; [reflexivity|].
      split; [intros r _; reflexivity|]. split; [apply munch_refl|].
      split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
      split; [intros _; reflexivity | intros H; exfalso; exact (H Z0)].
    + destruct (HA NZ) as (AF & AE & AG & gbs & MK & MW).
      pose proof (stk_not_ro m lo (bv_unsigned sp) A_EMPTY MI ST empty_ro) as EMP.
      assert (TB' : forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
          u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
          (p + (Z.of_nat (length n2) + 1) <= bv_unsigned sp - 17232 \/ bv_unsigned sp <= p)
          /\ apart_gnl p (Z.of_nat (length n2) + 1)
          /\ apart (bv_unsigned tp + ERRNO_TP_OFF) 4 p (Z.of_nat (length n2) + 1)
          /\ apart (bv_unsigned a0) MK_SIZE p (Z.of_nat (length n2) + 1)).
      { intros i n2 ix p E U. destruct (TB i n2 ix p E U) as (T1 & T2 & T3 & T4).
        split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. exact (T4 NZ). }
      eapply evt_mono.
      { eapply entry_ok with (kbs0 := kbs) (tab := tab) (gbs := gbs) (lo := lo);
          [exact HRD | exact HWR | exact HB | exact HMS | exact NZ | exact NL | exact FG | exact WF | exact OP
          | exact OB | exact CB | exact IT | exact EF | exact EG | exact TB' | exact AF | exact AE | exact AG
          | exact MK | exact MW | exact LO | exact SP | exact L0 | exact EMP | exact ST | exact MI | exact ER]. }
      intros ms' (regs' & m' & -> & RP & MU & WM & MI' & ST' & PO).
      exists regs', m'. split; [reflexivity|]. split; [exact RP|].
      split; [|split; [exact WM|split; [exact MI'|split; [exact ST'|exact PO]]]].
      replace (bv_unsigned a0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ).
      exact MU.
Qed.

(* closed: bcmp and memset by their released walks (lib/Prog/bcmp.v, lib/Prog/memset.v) *)
Theorem reac_served_unmark_all_closed :
  reac_link_alias_read_contract -> reac_link_alias_write_contract -> reac_served_unmark_all_contract.
Proof. intros HRD HWR. exact (reac_served_unmark_all_holds HRD HWR bcmp_holds memset_holds). Qed.
