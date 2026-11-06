(* reac_link_alias_write on image A: the MODEL side of the five refusal arms of the stretch
   +0x1a8 .. +0x1f0 (the piece `aw_mid_obl` of lib/A/Prog/reac_link_alias_writeDefs.v).

   What this file holds, and nothing else:
   - the value of lib/Prog/link_spec.v `write_lib` on each of the five refusals the code takes between the MID
     cut and the EXIT cut (name NULL, alias NULL, empty name, |alias| >= ALIAS_MAX, index 0), and the fact that
     each of them leaves the request list and the kernel state alone (the plain walk's `post_refuse`,
     lib/Prog/reac_link_alias_write.v:355-374, is the model);
   - the move of the fake kernel's views (`anlk_at`, `aiftab_at`) from the call's memory to a later memory that
     keeps g_nl's bytes (`aw_gnl_kept`) and the read set's bytes (the contract's `reac_link_alias_write_ard`);
   - `aw_pf_refuse`: the EXIT cut's result clause `aw_pf` for a refusal, from those two.

   The engine walk itself is lib/A/Prog/reac_link_alias_writeArmsB.v.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88 LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c reac_link_alias_write_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. link_spec's `write_lib` on the five refusals (no image, no memory)
   ========================================================================== *)

Lemma aw_wl_name_null : forall tab al reqs K,
  write_lib tab None al reqs K = Wres (- E_INVAL) reqs K.
Proof. intros tab al reqs K. reflexivity. Qed.

Lemma aw_wl_alias_null : forall tab nm reqs K,
  write_lib tab nm None reqs K = Wres (- E_INVAL) reqs K.
Proof. intros tab [s|] reqs K; reflexivity. Qed.

Lemma aw_wl_name_empty : forall tab al reqs K,
  write_lib tab (Some []) al reqs K = Wres (- E_INVAL) reqs K.
Proof. intros tab [a|] reqs K; reflexivity. Qed.

Lemma aw_wl_too_long : forall tab s a reqs K,
  s <> [] -> ALIAS_MAX <= Z.of_nat (length a) ->
  write_lib tab (Some s) (Some a) reqs K = Wres (- E_NAMETOOLONG) reqs K.
Proof.
  intros tab s a reqs K Hs Ha. unfold write_lib, write_core.
  replace (Nat.eqb (length s) 0) with false
    by (symmetry; apply Nat.eqb_neq; destruct s as [|b s']; [exact (fun _ => Hs eq_refl) | cbn; lia]).
  replace (ALIAS_MAX <=? Z.of_nat (length a)) with true by (symmetry; apply Z.leb_le; exact Ha).
  reflexivity.
Qed.

Lemma aw_wl_no_dev : forall tab s a reqs K,
  s <> [] -> Z.of_nat (length a) < ALIAS_MAX -> index_of tab s = 0 ->
  write_lib tab (Some s) (Some a) reqs K = Wres (- E_NODEV) reqs K.
Proof.
  intros tab s a reqs K Hs Ha Hi. unfold write_lib, write_core.
  replace (Nat.eqb (length s) 0) with false
    by (symmetry; apply Nat.eqb_neq; destruct s as [|b s']; [exact (fun _ => Hs eq_refl) | cbn; lia]).
  replace (ALIAS_MAX <=? Z.of_nat (length a)) with false by (symmetry; apply Z.leb_gt; exact Ha).
  rewrite Hi. reflexivity.
Qed.

(* The three return codes the code puts in s5, as the C library's errno values. *)
Lemma aw_rc_einval : - E_INVAL = -22. Proof. reflexivity. Qed.
Lemma aw_rc_etoolong : - E_NAMETOOLONG = -36. Proof. reflexivity. Qed.
Lemma aw_rc_enodev : - E_NODEV = -19. Proof. reflexivity. Qed.

(* A refusal leaves the request list and the kernel state as they were, which is all `aw_pf` needs of them. *)
Lemma aw_wl_keep : forall tab nm al reqs K,
  (forall s a, nm = Some s -> al = Some a ->
     s = [] \/ ALIAS_MAX <= Z.of_nat (length a) \/ index_of tab s = 0) ->
  w_reqs (write_lib tab nm al reqs K) = reqs /\ w_state (write_lib tab nm al reqs K) = K.
Proof.
  intros tab nm al reqs K H. unfold write_lib, write_core.
  destruct nm as [s|]; [|split; reflexivity].
  destruct al as [a|]; [|split; reflexivity].
  destruct (Nat.eqb (length s) 0) eqn:Es; [split; reflexivity|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)) eqn:Ea; [split; reflexivity|].
  destruct (H s a eq_refl eq_refl) as [Hs | [Hl | Hi]].
  - exfalso. rewrite Hs in Es. cbn in Es. discriminate Es.
  - exfalso. apply Z.leb_gt in Ea. lia.
  - rewrite Hi. cbn. split; reflexivity.
Qed.

(* The two `nlk_wf` consequences the Post's kernel clauses need when nothing moved. *)
Lemma aw_next_kstate : forall bs, nlk_wf bs -> Z.of_nat (k_next (nk_kstate bs)) = nk_next bs.
Proof. intros bs (_ & (Hlo & _) & _). cbn [nk_kstate k_next]. lia. Qed.

Lemma aw_n_sent_length : forall bs, nlk_wf bs -> Z.of_nat (length (nk_sent bs)) = nk_n_sent bs.
Proof.
  intros bs (_ & _ & (Hlo & _) & _). unfold nk_sent.
  rewrite length_map, length_seq. lia.
Qed.

(* ==========================================================================
   2. The A views of the fake kernel: they are determined by the memory, and they move with its bytes
   ========================================================================== *)

Section u.
Variable segs : list Segment.

Lemma aw_abytes_head : forall (m : word -> option byte) a b l,
  abytes segs m a (b :: l) -> mbyte segs m a = Some b.
Proof.
  intros m a b l (_ & _ & H). pose proof (H 0%nat ltac:(cbn; lia)) as H0.
  rewrite Z.add_0_r in H0. exact H0.
Qed.

Lemma aw_abytes_tail : forall (m : word -> option byte) a b l,
  abytes segs m a (b :: l) -> abytes segs m (a + 1) l.
Proof.
  intros m a b l (H0 & H1 & H2). cbn [length] in H1.
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia.
  exact (H2 (S i) ltac:(cbn [length] in *; lia)).
Qed.

Lemma aw_abytes_unique : forall (m : word -> option byte) a l1 l2,
  abytes segs m a l1 -> abytes segs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L.
  apply lw_list_ext; [exact L|]. intros i Hi.
  rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
Qed.

Lemma aw_acstr_unique : forall (m : word -> option byte) p s1 s2,
  acstr_at segs m p s1 -> acstr_at segs m p s2 -> s1 = s2.
Proof.
  intros m p s1. revert p.
  induction s1 as [|x s1 IH]; intros p s2 (B1 & N1) (B2 & N2); destruct s2 as [|y s2].
  - reflexivity.
  - exfalso. cbn [app] in B1, B2.
    pose proof (aw_abytes_head m p _ _ B1) as E1. pose proof (aw_abytes_head m p _ _ B2) as E2.
    rewrite E1 in E2. injection E2 as E2. apply N2. left. symmetry. exact E2.
  - exfalso. cbn [app] in B1, B2.
    pose proof (aw_abytes_head m p _ _ B1) as E1. pose proof (aw_abytes_head m p _ _ B2) as E2.
    rewrite E1 in E2. injection E2 as E2. apply N1. left. exact E2.
  - cbn [app] in B1, B2.
    pose proof (aw_abytes_head m p _ _ B1) as E1. pose proof (aw_abytes_head m p _ _ B2) as E2.
    rewrite E1 in E2. injection E2 as E2. subst y.
    f_equal. apply (IH (p + 1) s2).
    + split; [exact (aw_abytes_tail m p x _ B1) | intros Hin; apply N1; right; exact Hin].
    + split; [exact (aw_abytes_tail m p x _ B2) | intros Hin; apply N2; right; exact Hin].
Qed.

Lemma aw_astr_arg_unique : forall (m : word -> option byte) p o1 o2,
  astr_arg segs m p o1 -> astr_arg segs m p o2 -> o1 = o2.
Proof.
  intros m p [s1|] [s2|] H1 H2; cbn in H1, H2.
  - f_equal. exact (aw_acstr_unique m p s1 s2 (proj2 H1) (proj2 H2)).
  - exfalso. exact (proj1 H1 H2).
  - exfalso. exact (proj1 H2 H1).
  - reflexivity.
Qed.

Lemma aw_anlk_unique : forall (m : word -> option byte) g b1 b2,
  anlk_at segs m g b1 -> anlk_at segs m g b2 -> b1 = b2.
Proof.
  intros m g b1 b2 ((B1 & _) & L1) ((B2 & _) & L2).
  exact (aw_abytes_unique m g b1 b2 B1 B2 ltac:(lia)).
Qed.

(* a value a memory shows over n bytes is the only one in [0, 2 ^ (8 n)) it shows *)
Lemma aw_val_mem_det : forall (m : word -> option byte) a n v1 v2,
  val_mem segs m a n v1 -> val_mem segs m a n v2 ->
  0 <= v1 < 2 ^ (8 * Z.of_nat n) -> 0 <= v2 < 2 ^ (8 * Z.of_nat n) -> v1 = v2.
Proof.
  intros m a n v1 v2 H1 H2 R1 R2.
  assert (E : forall k, (k < n)%nat -> Z_to_bv 8 (le_byte v1 n k) = Z_to_bv 8 (le_byte v2 n k)).
  { intros k Hk. pose proof (H1 k Hk) as A1. pose proof (H2 k Hk) as A2.
    rewrite A1 in A2. injection A2 as A2. apply bv_eq. exact A2. }
  pose (l := map (fun k : nat => Z_to_bv 8 (le_byte v1 n k)) (seq 0 n)).
  assert (Hlen : length l = n) by (unfold l; rewrite length_map, length_seq; reflexivity).
  assert (L1 : bytes_le_to_Z l = v1).
  { apply (lw_bytes_of_vals n); [exact Hlen | exact R1 |].
    intros k Hk. unfold l.
    rewrite (lw_nth_error_map_seq (fun k : nat => Z_to_bv 8 (le_byte v1 n k)) n 0 k Hk).
    rewrite Nat.add_0_l. reflexivity. }
  assert (L2 : bytes_le_to_Z l = v2).
  { apply (lw_bytes_of_vals n); [exact Hlen | exact R2 |].
    intros k Hk. unfold l.
    rewrite (lw_nth_error_map_seq (fun k : nat => Z_to_bv 8 (le_byte v1 n k)) n 0 k Hk).
    rewrite Nat.add_0_l, (E k Hk). reflexivity. }
  rewrite <- L1, <- L2. reflexivity.
Qed.

Lemma aw_au64_det : forall (m : word -> option byte) a p1 p2,
  au64_at segs m a p1 -> au64_at segs m a p2 -> 0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 -> p1 = p2.
Proof.
  intros m a p1 p2 H1 H2 R1 R2.
  exact (aw_val_mem_det m a 8 p1 p2 H1 H2 ltac:(change (8 * Z.of_nat 8) with 64; lia)
           ltac:(change (8 * Z.of_nat 8) with 64; lia)).
Qed.

Lemma aw_au32_det : forall (m : word -> option byte) a v1 v2,
  au32_at segs m a v1 -> au32_at segs m a v2 -> 0 <= v1 < 2 ^ 31 -> 0 <= v2 < 2 ^ 31 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 R1 R2.
  exact (aw_val_mem_det m a 4 v1 v2 H1 H2 ltac:(change (8 * Z.of_nat 4) with 32; lia)
           ltac:(change (8 * Z.of_nat 4) with 32; lia)).
Qed.

Lemma aw_acstr_range : forall (m : word -> option byte) p s,
  acstr_at segs m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof.
  intros m p s ((H0 & H1 & _) & _). rewrite length_app in H1. cbn [length] in H1. lia.
Qed.

Lemma aw_aiftab_unique : forall (m : word -> option byte) g bs t1 t2,
  aiftab_at segs m g bs t1 -> aiftab_at segs m g bs t2 -> t1 = t2.
Proof.
  intros m g bs t1 t2 (L1 & _ & H1) (L2 & _ & H2).
  apply nth_error_ext. intros i.
  destruct (nth_error t1 i) as [[n1 x1]|] eqn:E1; destruct (nth_error t2 i) as [[n2 x2]|] eqn:E2.
  - destruct (H1 i n1 x1 E1) as (R1 & p1 & U1 & _ & C1 & I1).
    destruct (H2 i n2 x2 E2) as (R2 & p2 & U2 & _ & C2 & I2).
    pose proof (aw_acstr_range m p1 n1 C1) as Hr1. pose proof (aw_acstr_range m p2 n2 C2) as Hr2.
    assert (p1 = p2) as -> by (apply (aw_au64_det m _ p1 p2 U1 U2); lia).
    rewrite (aw_acstr_unique m p2 n1 n2 C1 C2), (aw_au32_det m _ x1 x2 I1 I2 R1 R2). reflexivity.
  - exfalso. assert (Hi1 : (i < length t1)%nat) by (apply nth_error_Some; rewrite E1; discriminate).
    apply nth_error_None in E2. lia.
  - exfalso. assert (Hi2 : (i < length t2)%nat) by (apply nth_error_Some; rewrite E2; discriminate).
    apply nth_error_None in E1. lia.
  - reflexivity.
Qed.

(* ---- the same views at a later memory that keeps the bytes ---- *)

Lemma aw_abytes_move : forall (m m' : word -> option byte) a l,
  abytes segs m a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> mbyte segs m' x = mbyte segs m x) ->
  abytes segs m' a l.
Proof.
  intros m m' a l (H0 & H1 & H2) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (HK (a + Z.of_nat i) ltac:(lia)). exact (H2 i Hi).
Qed.

Lemma aw_acstr_move : forall (m m' : word -> option byte) p s,
  acstr_at segs m p s ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> mbyte segs m' x = mbyte segs m x) ->
  acstr_at segs m' p s.
Proof.
  intros m m' p s (B & N) HK. split; [|exact N].
  apply (aw_abytes_move m m' p (s ++ [zb 0]) B).
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply HK. lia.
Qed.

Lemma aw_val_mem_move : forall (m m' : word -> option byte) a n v,
  val_mem segs m a n v ->
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m' a n v.
Proof. intros m m' a n v H HK k Hk. rewrite (HK (a + Z.of_nat k) ltac:(lia)). exact (H k Hk). Qed.

Lemma aw_anlk_move : forall (m m' : word -> option byte) g bs,
  anlk_at segs m g bs ->
  (forall x, g <= x < g + NK_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, g <= x < g + NK_SIZE -> writable_at segs m' x) ->
  anlk_at segs m' g bs.
Proof.
  intros m m' g bs ((B & _) & L) HK HW. split; [split|exact L].
  - apply (aw_abytes_move m m' g bs B). intros x Hx. apply HK. lia.
  - intros i Hi. apply HW. lia.
Qed.

Lemma aw_aiftab_move : forall (m m' : word -> option byte) g bs tab,
  aiftab_at segs m g bs tab ->
  (forall x, g <= x < g + NK_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at segs m (g + NK_IF_NAME + 8 * Z.of_nat i) p -> acstr_at segs m p n2 ->
     forall x, p <= x <= p + Z.of_nat (length n2) -> mbyte segs m' x = mbyte segs m x) ->
  aiftab_at segs m' g bs tab.
Proof.
  intros m m' g bs tab (L1 & L2 & H) HK HS.
  split; [exact L1|]. split; [exact L2|].
  intros i n2 ix Hi. destruct (H i n2 ix Hi) as (Rx & p & U & Hp0 & C & I).
  assert (Hilt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  split; [exact Rx|]. exists p.
  split.
  { apply (aw_val_mem_move m m' _ 8 p U). intros x Hx.
    apply HK. change (Z.of_nat 8) with 8 in Hx.
    unfold NK_IF_NAME, NK_SIZE in *. lia. }
  split; [exact Hp0|]. split.
  { apply (aw_acstr_move m m' p n2 C). intros x Hx. exact (HS i n2 ix p Hi U C x Hx). }
  apply (aw_val_mem_move m m' _ 4 ix I). intros x Hx.
  apply HK. change (Z.of_nat 4) with 4 in Hx.
  unfold NK_IF_INDEX, NK_SIZE in *. lia.
Qed.

End u.
