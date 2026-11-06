(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetDeallocInstA.v, with its module paths changed; 2 of its 85 lines of code are new or changed and 1 line of the source is left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetDeallocInstA.v, with its module paths and module names changed; 397 of its 419 lines of code are new or changed and 63 lines of the source are left out. *)
(* reac_link_alias_read on image A (lib/A/Prog/reac_link_alias_read_c.v): the pure byte algebra over the A views of
   lib/A/Prog/link_amem.v and the two builders of its Post `reac_link_alias_read_apost`, the lemmas the walk ends
   with. The image-A twins of the plain walk's sections 2-4 (lib/Prog/reac_link_alias_read.v on
   the plain side): no symbolic engine, no journal, no image instance.

   Proves no function (kind: segment lemma of reac_link_alias_read's walk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem reac_link_alias_read_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section ar.
Variable segs : list Segment.

(* ==========================================================================
   1. Uniqueness: the Post quantifies afresh over the kernel bytes, the table and the name
   ========================================================================== *)

(* the n little-endian bytes of a value fix it modulo 2 ^ (8 n) *)
Lemma ar_lb_inj : forall (n : nat) (p1 p2 : Z),
  (forall k, (k < n)%nat ->
     Z_to_bv 8 (Z.shiftr (p1 mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256) =
     Z_to_bv 8 (Z.shiftr (p2 mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256)) ->
  p1 mod 2 ^ (8 * Z.of_nat n) = p2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n p1 p2 H. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i (8 * Z.of_nat n)) as [Hl|Hl].
  - pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hr.
    set (q := i / 8) in *. set (r := i mod 8) in *. clearbody q r.
    assert (Hq : 0 <= q) by lia.
    assert (Hk : (Z.to_nat q < n)%nat) by lia.
    specialize (H (Z.to_nat q) Hk).
    apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
    change (bv_modulus 8) with 256 in H. rewrite !Z.mod_mod in H by lia.
    rewrite Z2Nat.id in H by exact Hq.
    apply (f_equal (fun z => Z.testbit z r)) in H. cbv beta in H.
    change 256 with (2 ^ 8) in H. rewrite !Z.mod_pow2_bits_low in H by lia.
    rewrite !Z.shiftr_spec in H by lia.
    replace (r + 8 * q) with i in H by lia. exact H.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma ar_vm_unique : forall m a (n : nat) v1 v2, val_mem segs m a n v1 -> val_mem segs m a n v2 ->
  v1 mod 2 ^ (8 * Z.of_nat n) = v2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros m a n v1 v2 H1 H2. apply ar_lb_inj. intros k Hk.
  pose proof (eq_trans (eq_sym (H1 k Hk)) (H2 k Hk)) as E.
  exact (f_equal (fun o : option byte => match o with Some b => b | None => Z_to_bv 8 0 end) E).
Qed.

Lemma ar_abytes_unique : forall m a l1 l2,
  abytes segs m a l1 -> abytes segs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 i) Hi), (proj2 (nth_error_None l2 i) ltac:(lia)). reflexivity.
Qed.

(* a shorter C string at the same address would put its NUL inside the longer one *)
Lemma ar_acstr_short : forall m a s1 s2, acstr_at segs m a s1 -> acstr_at segs m a s2 ->
  (length s1 < length s2)%nat -> False.
Proof.
  intros m a s1 s2 [(_ & _ & B1) _] [(_ & _ & B2) N2] L.
  assert (E1 : mbyte segs m (a + Z.of_nat (length s1)) = Some (zb 0)).
  { rewrite (B1 (length s1)) by (rewrite length_app; cbn [length]; lia).
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (E2 : mbyte segs m (a + Z.of_nat (length s1)) = nth_error s2 (length s1)).
  { rewrite (B2 (length s1)) by (rewrite length_app; cbn [length]; lia).
    apply nth_error_app1. exact L. }
  apply N2. apply (nth_error_In s2 (length s1)). rewrite <- E2. exact E1.
Qed.

Lemma ar_acstr_unique : forall m a s1 s2, acstr_at segs m a s1 -> acstr_at segs m a s2 -> s1 = s2.
Proof.
  intros m a s1 s2 H1 H2.
  destruct (Nat.lt_trichotomy (length s1) (length s2)) as [L|[L|L]].
  - exfalso. exact (ar_acstr_short m a s1 s2 H1 H2 L).
  - destruct H1 as [B1 _]. destruct H2 as [B2 _].
    apply (app_inv_tail [zb 0]). apply (ar_abytes_unique m a); [exact B1 | exact B2 |].
    rewrite !length_app, L. reflexivity.
  - exfalso. exact (ar_acstr_short m a s2 s1 H2 H1 L).
Qed.

Lemma ar_anlk_unique : forall m g b1 b2, anlk_at segs m g b1 -> anlk_at segs m g b2 -> b1 = b2.
Proof.
  intros m g b1 b2 [[B1 _] L1] [[B2 _] L2]. apply (ar_abytes_unique m g); [exact B1 | exact B2 | lia].
Qed.

Lemma ar_au64_unique : forall m a p1 p2, au64_at segs m a p1 -> au64_at segs m a p2 ->
  p1 mod 2 ^ 64 = p2 mod 2 ^ 64.
Proof.
  intros m a p1 p2 H1 H2. pose proof (ar_vm_unique m a 8 p1 p2 H1 H2) as E.
  change (8 * Z.of_nat 8) with 64 in E. exact E.
Qed.

Lemma ar_au32_small_unique : forall m a x1 x2, au32_at segs m a x1 -> au32_at segs m a x2 ->
  0 <= x1 < 2 ^ 31 -> 0 <= x2 < 2 ^ 31 -> x1 = x2.
Proof.
  intros m a x1 x2 H1 H2 R1 R2. pose proof (ar_vm_unique m a 4 x1 x2 H1 H2) as E.
  change (8 * Z.of_nat 4) with 32 in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma ar_acstr_range : forall m p s, acstr_at segs m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof.
  intros m p s [(Ha & Hl & _) _]. rewrite length_app in Hl. cbn [length] in Hl. lia.
Qed.

Lemma ar_aiftab_unique : forall m bs tab1 tab2,
  aiftab_at segs m LA_G_NL bs tab1 -> aiftab_at segs m LA_G_NL bs tab2 -> tab1 = tab2.
Proof.
  intros m bs tab1 tab2 (L1 & _ & E1) (L2 & _ & E2).
  assert (L : length tab1 = length tab2) by lia.
  apply nth_error_ext. intros i.
  destruct (nth_error tab1 i) as [[n1 x1]|] eqn:H1; destruct (nth_error tab2 i) as [[n2 x2]|] eqn:H2.
  - destruct (E1 i n1 x1 H1) as (R1 & p1 & P1 & _ & C1 & I1).
    destruct (E2 i n2 x2 H2) as (R2 & p2 & P2 & _ & C2 & I2).
    pose proof (ar_au64_unique _ _ _ _ P1 P2) as Ep.
    pose proof (ar_acstr_range _ _ _ C1). pose proof (ar_acstr_range _ _ _ C2).
    rewrite !Z.mod_small in Ep by lia. subst p2.
    rewrite (ar_acstr_unique _ _ _ _ C1 C2).
    rewrite (ar_au32_small_unique _ _ _ _ I1 I2 R1 R2). reflexivity.
  - exfalso. apply nth_error_None in H2. assert (i < length tab1)%nat by (apply nth_error_Some; congruence). lia.
  - exfalso. apply nth_error_None in H1. assert (i < length tab2)%nat by (apply nth_error_Some; congruence). lia.
  - reflexivity.
Qed.

Lemma ar_astr_arg_unique : forall m a o1 o2, astr_arg segs m a o1 -> astr_arg segs m a o2 -> o1 = o2.
Proof.
  intros m a [s1|] [s2|] H1 H2; cbn [astr_arg] in H1, H2.
  - f_equal. exact (ar_acstr_unique m a s1 s2 (proj2 H1) (proj2 H2)).
  - destruct H1 as [Hn _]. contradiction.
  - destruct H2 as [Hn _]. contradiction.
  - reflexivity.
Qed.

(* ==========================================================================
   2. Transport: a view survives a memory change that keeps its bytes
   ========================================================================== *)

Lemma ar_abytes_move : forall (m m' : word -> option byte) a bs,
  abytes segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte segs m' x = mbyte segs m x) ->
  abytes segs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & H) Hk. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite (Hk (a + Z.of_nat i)) by lia. exact (H i Hi).
Qed.

Lemma ar_acstr_move : forall m m' p s, acstr_at segs m p s ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> mbyte segs m' x = mbyte segs m x) -> acstr_at segs m' p s.
Proof.
  intros m m' p s [B N] Hk. split; [|exact N]. apply (ar_abytes_move m m' p _ B).
  intros x Hx. apply Hk. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma ar_au8arr_move : forall m m' a bs, au8arr segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> writable_at segs m' x) -> au8arr segs m' a bs.
Proof.
  intros m m' a bs [B R] Hk Hw. split; [exact (ar_abytes_move m m' a bs B Hk)|].
  intros i Hi. apply Hw. lia.
Qed.

Lemma ar_anlk_move : forall m m' bs, anlk_at segs m LA_G_NL bs ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> writable_at segs m' x) -> anlk_at segs m' LA_G_NL bs.
Proof.
  intros m m' bs [U L] Hk Hw. split; [|exact L].
  apply (ar_au8arr_move m m' LA_G_NL bs U); intros x Hx; [apply Hk | apply Hw]; lia.
Qed.

Lemma ar_abuf_move : forall m m' p n, abuf segs m p n ->
  (forall x, p <= x < p + n -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, p <= x < p + n -> writable_at segs m' x) -> abuf segs m' p n.
Proof.
  intros m m' p n (junk & L & U) Hk Hw. exists junk. split; [exact L|].
  apply (ar_au8arr_move m m' p junk U); intros x Hx; [apply Hk | apply Hw]; lia.
Qed.

Lemma ar_aiftab_keep : forall m m' bs bs' tab,
  aiftab_at segs m LA_G_NL bs tab -> nk_n_if bs' = nk_n_if bs ->
  (forall x, LA_G_NL + NK_IF_NAME <= x < LA_G_NL + NK_IF_NAME + 8 * Z.of_nat (length tab) ->
     mbyte segs m' x = mbyte segs m x) ->
  (forall x, LA_G_NL + NK_IF_INDEX <= x < LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat (length tab) ->
     mbyte segs m' x = mbyte segs m x) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     forall x, p <= x <= p + Z.of_nat (length n2) -> mbyte segs m' x = mbyte segs m x) ->
  aiftab_at segs m' LA_G_NL bs' tab.
Proof.
  intros m m' bs bs' tab (L & L80 & E) Hn DN DI DS.
  split; [rewrite Hn; exact L|]. split; [exact L80|]. intros i n2 ix Hi.
  destruct (E i n2 ix Hi) as (R & p & P & Pz & C & I). split; [exact R|].
  assert (Li : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  exists p. split; [|split; [exact Pz|split]].
  - unfold au64_at, val_mem in *. intros k Hk.
    rewrite (DN (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i + Z.of_nat k)) by lia. exact (P k Hk).
  - pose proof (ar_acstr_range m p n2 C) as Rp.
    apply (ar_acstr_move m m' p n2 C). exact (DS i n2 ix p Hi P ltac:(lia)).
  - unfold au32_at, val_mem in *. intros k Hk.
    rewrite (DI (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat i + Z.of_nat k)) by lia. exact (I k Hk).
Qed.

(* ==========================================================================
   3. Pure facts of the model
   ========================================================================== *)

Lemma ar_index_of_range : forall tab s,
  (forall i n ix, nth_error tab i = Some (n, ix) -> 0 <= ix < 2 ^ 31) -> 0 <= index_of tab s < 2 ^ 31.
Proof.
  induction tab as [|[n ix] tab IH]; intros s H; cbn [index_of]; [lia|].
  destruct (bl_eqb n s).
  - exact (H 0%nat n ix eq_refl).
  - apply IH. intros i n2 ix2 E. exact (H (S i) n2 ix2 E).
Qed.

Lemma ar_talk_after_sock : forall K, k_sock (talk_after K) = 0.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [reflexivity|].
  destruct (negb (k_send K =? 0)); [reflexivity|].
  destruct (chunk_loop _ _ _) as [v j]. destruct v; reflexivity.
Qed.

Lemma ar_nk_sent_length : forall bs, 0 <= nk_n_sent bs -> Z.of_nat (length (nk_sent bs)) = nk_n_sent bs.
Proof. intros bs H. unfold nk_sent. rewrite length_map, length_seq. lia. Qed.

Lemma ar_read_lib_none : forall tab kc ac reqs K,
  read_lib tab None kc ac reqs K = Rres (- E_INVAL) [] [] reqs K.
Proof. intros. reflexivity. Qed.

Lemma ar_read_lib_empty : forall tab kc ac reqs K,
  read_lib tab (Some []) kc ac reqs K = Rres (- E_INVAL) [] [] reqs K.
Proof. intros. reflexivity. Qed.

Lemma ar_read_lib_nodev : forall tab s kc ac reqs K, s <> [] -> index_of tab s = 0 ->
  read_lib tab (Some s) kc ac reqs K = Rres (- E_NODEV) [] [] reqs K.
Proof.
  intros tab s kc ac reqs K Hs Hi. unfold read_lib, read_core.
  destruct s as [|b s']; [exfalso; exact (Hs eq_refl)|].
  cbn [length Nat.eqb]. cbv zeta. rewrite Hi. reflexivity.
Qed.

Lemma ar_read_lib_talk : forall tab s kc ac reqs K, s <> [] -> index_of tab s <> 0 ->
  read_lib tab (Some s) kc ac reqs K =
    Rres (talk_rc_lib K)
         (if kc <? 1 then [] else text_of_attr (a_kind (talk_attrs K)) kc)
         (if ac <? 1 then [] else text_of_attr (a_alias (talk_attrs K)) ac)
         (if talk_owes K then owe reqs (req_read (index_of tab s)) else reqs)
         (talk_after K).
Proof.
  intros tab s kc ac reqs K Hs Hi. unfold read_lib, read_core.
  destruct s as [|b s']; [exfalso; exact (Hs eq_refl)|].
  cbn [length Nat.eqb]. cbv zeta.
  rewrite (proj2 (Z.eqb_neq (index_of tab (b :: s')) 0) Hi). reflexivity.
Qed.

(* ==========================================================================
   4. The two Post builders (the walk ends with one of these)
   ========================================================================== *)

(* the three arms that return a code and leave both buffers empty: NULL name, empty name, unknown name *)
Lemma ar_post_refuse : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) kbs tab nm rc,
  anlk_at segs m LA_G_NL kbs -> aiftab_at segs m LA_G_NL kbs tab -> astr_arg segs m (aarg regs 0) nm ->
  nlk_wf kbs -> nk_open kbs = 0 ->
  read_lib tab nm (aarg regs 2) (aarg regs 4) (nk_sent kbs) (nk_kstate kbs)
    = Rres rc [] [] (nk_sent kbs) (nk_kstate kbs) ->
  getr regs' 10 = w64 rc ->
  anlk_at segs m' LA_G_NL kbs -> aiftab_at segs m' LA_G_NL kbs tab ->
  (aarg regs 1 <> 0 -> 1 <= aarg regs 2 -> acstr_at segs m' (aarg regs 1) [] /\ abuf segs m' (aarg regs 1) (aarg regs 2)) ->
  (aarg regs 3 <> 0 -> 1 <= aarg regs 4 -> acstr_at segs m' (aarg regs 3) [] /\ abuf segs m' (aarg regs 3) (aarg regs 4)) ->
  reac_link_alias_read_apost segs regs m regs' m'.
Proof.
  intros regs regs' m m' kbs tab nm rc NK IT SN WF OP ER RC NK' IT' BK BA.
  intros kbs2 tab2 nm2 NK2 IT2 SN2.
  assert (kbs2 = kbs) by exact (ar_anlk_unique _ _ _ _ NK2 NK). subst kbs2.
  assert (tab2 = tab) by exact (ar_aiftab_unique _ _ _ _ IT2 IT). subst tab2.
  assert (nm2 = nm) by exact (ar_astr_arg_unique _ _ _ _ SN2 SN). subst nm2.
  cbv zeta. rewrite ER. cbn [r_rc r_kind r_alias r_reqs r_state].
  pose proof WF as WF'. destruct WF' as (W1 & W2 & W3 & _).
  split; [exact RC|].
  split.
  - exists kbs. split; [exact NK'|]. split; [exact WF|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact IT'|].
    split; [cbn [k_next nk_kstate]; lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [symmetry; apply ar_nk_sent_length; lia|].
    split; [exact OP|split; [reflexivity|split; [reflexivity|split; [lia|intros _; reflexivity]]]].
  - split; [intros H1 H2; exact (proj1 (BK H1 H2))|].
    split; [intros H1 H2; exact (proj1 (BA H1 H2))|].
    split; [intros H1 H2; exact (proj2 (BK H1 H2))|].
    intros H1 H2; exact (proj2 (BA H1 H2)).
Qed.

(* the arm that calls nl_talk *)
Lemma ar_post_talk : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) kbs tab s,
  anlk_at segs m LA_G_NL kbs -> aiftab_at segs m LA_G_NL kbs tab ->
  astr_arg segs m (aarg regs 0) (Some s) -> nlk_wf kbs -> s <> [] -> index_of tab s <> 0 ->
  getr regs' 10 = w64 (talk_rc_lib (nk_kstate kbs)) ->
  (exists kbs', anlk_at segs m' LA_G_NL kbs' /\ nlk_wf kbs'
     /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
     /\ nk_n_if kbs' = nk_n_if kbs
     /\ aiftab_at segs m' LA_G_NL kbs' tab
     /\ nk_socket_errno kbs' = 0
     /\ nk_send_errno kbs' = k_send (talk_after (nk_kstate kbs))
     /\ nk_next kbs' = Z.of_nat (k_next (talk_after (nk_kstate kbs)))
     /\ nk_sent kbs' = (if talk_owes (nk_kstate kbs)
                        then owe (nk_sent kbs) (req_read (index_of tab s)) else nk_sent kbs)
     /\ nk_n_sent kbs' = Z.of_nat (length (nk_sent kbs'))
     /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
     /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
     /\ (nk_socket_errno kbs <> 0 -> nk_opened kbs' = nk_opened kbs)
     /\ (nk_socket_errno kbs = 0 -> nk_opened kbs' = nk_opened kbs + 1)) ->
  (forall pay, a_kind (talk_attrs (nk_kstate kbs)) = Some pay -> aarg regs 1 <> 0 -> 1 <= aarg regs 2 ->
     acstr_at segs m' (aarg regs 1) (cut_text pay (aarg regs 2))) ->
  (forall pay, a_alias (talk_attrs (nk_kstate kbs)) = Some pay -> aarg regs 3 <> 0 -> 1 <= aarg regs 4 ->
     acstr_at segs m' (aarg regs 3) (cut_text pay (aarg regs 4))) ->
  (a_kind (talk_attrs (nk_kstate kbs)) = None -> aarg regs 1 <> 0 -> 1 <= aarg regs 2 ->
     acstr_at segs m' (aarg regs 1) []) ->
  (a_alias (talk_attrs (nk_kstate kbs)) = None -> aarg regs 3 <> 0 -> 1 <= aarg regs 4 ->
     acstr_at segs m' (aarg regs 3) []) ->
  (aarg regs 1 <> 0 -> 1 <= aarg regs 2 -> abuf segs m' (aarg regs 1) (aarg regs 2)) ->
  (aarg regs 3 <> 0 -> 1 <= aarg regs 4 -> abuf segs m' (aarg regs 3) (aarg regs 4)) ->
  reac_link_alias_read_apost segs regs m regs' m'.
Proof.
  intros regs regs' m m' kbs tab s NK IT SN WF Sne Inz RC NL KS AS KN AN KR AR.
  intros kbs2 tab2 nm2 NK2 IT2 SN2.
  assert (kbs2 = kbs) by exact (ar_anlk_unique _ _ _ _ NK2 NK). subst kbs2.
  assert (tab2 = tab) by exact (ar_aiftab_unique _ _ _ _ IT2 IT). subst tab2.
  assert (nm2 = Some s) by exact (ar_astr_arg_unique _ _ _ _ SN2 SN). subst nm2.
  cbv zeta.
  rewrite (ar_read_lib_talk tab s (aarg regs 2) (aarg regs 4) (nk_sent kbs) (nk_kstate kbs) Sne Inz).
  cbn [r_rc r_kind r_alias r_reqs r_state].
  split; [exact RC|].
  split.
  - destruct NL as (kbs' & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16).
    exists kbs'. split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|].
    split; [exact N5|]. split; [exact N6|]. split; [exact N9|].
    split; [rewrite ar_talk_after_sock; exact N7|]. split; [exact N8|]. split; [exact N10|].
    split; [rewrite N11, N10; reflexivity|]. split; [exact N12|]. split; [exact N13|]. split; [exact N14|].
    split; [destruct (Z.eq_dec (nk_socket_errno kbs) 0) as [E|E]; [rewrite (N16 E) | rewrite (N15 E)]; lia|].
    intros [H|[H|H]];
      [discriminate H | injection H as H; exfalso; exact (Sne H) | exfalso; exact (Inz (H s eq_refl))].
  - assert (KC : forall c, 1 <= c -> (c <? 1) = false) by (intros c Hc; apply Z.ltb_ge; lia).
    split.
    { intros H1 H2. rewrite (KC _ H2). unfold text_of_attr.
      destruct (a_kind (talk_attrs (nk_kstate kbs))) as [pay|] eqn:Ek;
        [first [exact (KS pay Ek H1 H2) | exact (KS pay eq_refl H1 H2)]
        |first [exact (KN Ek H1 H2) | exact (KN eq_refl H1 H2)]]. }
    split.
    { intros H1 H2. rewrite (KC _ H2). unfold text_of_attr.
      destruct (a_alias (talk_attrs (nk_kstate kbs))) as [pay|] eqn:Ea;
        [first [exact (AS pay Ea H1 H2) | exact (AS pay eq_refl H1 H2)]
        |first [exact (AN Ea H1 H2) | exact (AN eq_refl H1 H2)]]. }
    split; [exact KR | exact AR].
Qed.

(* ==========================================================================
   5. The request the code builds in its class-1 side frame (the four header stores at +0x1b4..+0x1c0 and the
      checked_memset of [q + 12, q + 32)), read back as the model's byte list `req_read idx`
   ========================================================================== *)

Lemma ar_nth_Z_to_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

(* a little-endian byte of a value inside its width is a plain shift *)
Lemma ar_lb_small : forall v (n k : nat), 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  Z_to_bv 8 (Z.shiftr (v mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256) =
  Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v n k Hv. rewrite (Z.mod_small v) by exact Hv. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma ar_nth_repeat : forall (b : byte) n i, (i < n)%nat -> nth_error (repeat b n) i = Some b.
Proof.
  induction n as [|n IH]; intros i Hi; [lia|]. destruct i as [|i]; [reflexivity|].
  cbn [repeat nth_error]. apply IH. lia.
Qed.

Lemma ar_length_repeat : forall (b : byte) n, length (repeat b n) = n.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat length]. rewrite IH. reflexivity. Qed.

Lemma ar_bytes_map_inj : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma ar_len_le4 : forall v, Z.of_nat (length (Z_to_le_bytes 4 v)) = 4.
Proof. intros v. reflexivity. Qed.

Lemma ar_len_zeros8 : Z.of_nat (length (zeros 8)) = 8.
Proof. reflexivity. Qed.

Lemma ar_abytes_app_at : forall m a b l1 l2, b = a + Z.of_nat (length l1) ->
  abytes segs m a l1 -> abytes segs m b l2 -> abytes segs m a (l1 ++ l2).
Proof.
  intros m a b l1 l2 Eb (H1a & H1b & H1) (H2a & H2b & H2). subst b.
  split; [exact H1a|]. split; [rewrite length_app; lia|].
  intros i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length l1)) as [Hl|Hl].
  - rewrite nth_error_app1 by exact Hl. exact (H1 i Hl).
  - rewrite nth_error_app2 by exact Hl.
    replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia.
    apply H2. lia.
Qed.

(* a 4-byte little-endian field the code stored, as the model's Z_to_le_bytes *)
Lemma ar_abytes_val4 : forall m a v, 0 <= a -> a + 4 <= 2 ^ 64 -> 0 <= v < 2 ^ 32 ->
  val_mem segs m a 4 v -> abytes segs m a (Z_to_le_bytes 4 v).
Proof.
  intros m a v Ha Hb Hv H. split; [exact Ha|]. split; [rewrite ar_len_le4; lia|].
  intros i Hi. change (length (Z_to_le_bytes 4 v)) with 4%nat in Hi.
  rewrite (ar_nth_Z_to_le_bytes 4 v i Hi). rewrite <- (ar_lb_small v 4 i Hv). exact (H i Hi).
Qed.

(* n bytes the memset zeroed, as the model's zeros *)
Lemma ar_abytes_zeros : forall m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> mbyte segs m (a + i) = Some (Z_to_bv 8 0)) -> abytes segs m a (zeros n).
Proof.
  intros m a n Ha Hn Hb H. unfold zeros. split; [exact Ha|]. split; [rewrite ar_length_repeat; lia|].
  intros i Hi. rewrite ar_length_repeat in Hi. rewrite (ar_nth_repeat (zb 0) _ i Hi).
  exact (H (Z.of_nat i) ltac:(lia)).
Qed.

(* the 32 bytes of req_read, field by field as the code stores them *)
Lemma ar_req_read_eq : forall idx, req_read idx =
  Z_to_le_bytes 4 32 ++ Z_to_le_bytes 4 65554 ++ Z_to_le_bytes 4 1 ++ zeros 8 ++ Z_to_le_bytes 4 idx ++ zeros 8.
Proof.
  intros idx. unfold req_read, req_head.
  replace (Z_to_le_bytes 4 65554) with (Z_to_le_bytes 2 RTM_GETLINK ++ Z_to_le_bytes 2 F_REQUEST)
    by (apply ar_bytes_map_inj; vm_compute; reflexivity).
  rewrite <- !app_assoc. first [reflexivity | vm_compute; reflexivity].
Qed.

Lemma ar_req_bytes : forall (m : word -> option byte) q idx,
  0 <= idx < 2 ^ 31 -> 0 <= q -> q + 32 <= 2 ^ 64 ->
  val_mem segs m q 4 32 ->
  val_mem segs m (q + 4) 4 65554 ->
  val_mem segs m (q + 8) 4 1 ->
  val_mem segs m (q + 20) 4 idx ->
  (forall i, 0 <= i < 8 -> mbyte segs m (q + 12 + i) = Some (Z_to_bv 8 0)) ->
  (forall i, 0 <= i < 8 -> mbyte segs m (q + 24 + i) = Some (Z_to_bv 8 0)) ->
  abytes segs m q (req_read idx).
Proof.
  intros m q idx Hidx Hq Hq32 V0 V1 V2 V3 Z1 Z2. rewrite ar_req_read_eq.
  apply (ar_abytes_app_at m q (q + 4));
    [rewrite ar_len_le4; lia | apply ar_abytes_val4; [lia | lia | lia | exact V0] |].
  apply (ar_abytes_app_at m (q + 4) (q + 8));
    [rewrite ar_len_le4; lia | apply ar_abytes_val4; [lia | lia | lia | exact V1] |].
  apply (ar_abytes_app_at m (q + 8) (q + 12));
    [rewrite ar_len_le4; lia | apply ar_abytes_val4; [lia | lia | lia | exact V2] |].
  apply (ar_abytes_app_at m (q + 12) (q + 20));
    [rewrite ar_len_zeros8; lia | apply ar_abytes_zeros; [lia | lia | lia | exact Z1] |].
  apply (ar_abytes_app_at m (q + 20) (q + 24));
    [rewrite ar_len_le4; lia | apply ar_abytes_val4; [lia | lia | lia | exact V3] |].
  apply ar_abytes_zeros; [lia | lia | lia | exact Z2].
Qed.

Lemma ar_req_read_length : forall idx, Z.of_nat (length (req_read idx)) = 32.
Proof. intros idx. rewrite ar_req_read_eq. reflexivity. Qed.

End ar.

About ar_post_refuse. About ar_post_talk.
Print Assumptions ar_post_talk.
About ar_req_bytes.
Print Assumptions ar_req_bytes.
