(* The op_unmark arm (c3), plain image: kernel_c.v's Pre at the arm's call of kernel (0x13b28, a0 = sp + 0x40),
   from the pieces of lh_mem: the cursor cells, the payload, the fake kernel, the interface table and where
   its names live, texts[] and its strings (read-only image bytes), and long_alias. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC3Lib LC3Keep.
Local Open Scope Z_scope.

(* ==========================================================================
   1. C strings
   ========================================================================== *)

Lemma c3_bytes_at_cons : forall m a b l, bytes_at rsegs m a (b :: l) ->
  mrd rsegs m (wa a) = Some b /\ bytes_at rsegs m (a + 1) l.
Proof.
  intros m a b l H. change (b :: l) with ([b] ++ l) in H.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in H. destruct H as [H1 H2]. split; [|exact H2].
  destruct H1 as (_ & _ & H1). specialize (H1 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in H1. exact H1.
Qed.

Lemma c3_cstr_uniq : forall s1 m a s2 r, bytes_at rsegs m a (s1 ++ [zb 0]) -> ~ In (zb 0) s1 ->
  bytes_at rsegs m a (s2 ++ zb 0 :: r) -> ~ In (zb 0) s2 -> s1 = s2.
Proof.
  induction s1 as [|b1 s1 IH]; intros m a s2 r H1 N1 H2 N2; destruct s2 as [|b2 s2]; cbn [app] in H1, H2.
  - reflexivity.
  - apply c3_bytes_at_cons in H1 as [E1 _]. apply c3_bytes_at_cons in H2 as [E2 _].
    rewrite E1 in E2. injection E2 as E2. exfalso. apply N2. left. congruence.
  - apply c3_bytes_at_cons in H1 as [E1 _]. apply c3_bytes_at_cons in H2 as [E2 _].
    rewrite E1 in E2. injection E2 as E2. exfalso. apply N1. left. congruence.
  - apply c3_bytes_at_cons in H1 as [E1 T1]. apply c3_bytes_at_cons in H2 as [E2 T2].
    rewrite E1 in E2. injection E2 as E2. subst b2. f_equal.
    apply (IH m (a + 1) s2 r T1); [intros HI; apply N1; right; exact HI | exact T2 | intros HI; apply N2; right; exact HI].
Qed.

(* ==========================================================================
   2. texts[]: its eleven strings, read from the read-only image
   ========================================================================== *)

Fixpoint c3_rstr (a : Z) (fuel : nat) : list byte :=
  match fuel with
  | O => []
  | S f => match seg_rom rsegs (Z_to_bv 64 a) with
           | Some b => if bz b =? 0 then [] else b :: c3_rstr (a + 1) f
           | None => []
           end
  end.

Fixpoint c3_rbytes (a : Z) (n : nat) : list byte :=
  match n with
  | O => []
  | S k => match seg_rom rsegs (Z_to_bv 64 a) with Some b => b :: c3_rbytes (a + 1) k | None => [] end
  end.

Definition c3_txt_s (p : Z) : list byte := c3_rstr p 64.
Definition c3_txt_slack (p : Z) : list byte :=
  c3_rbytes (p + Z.of_nat (length (c3_txt_s p)) + 1) (Z.to_nat ((- (p + Z.of_nat (length (c3_txt_s p)) + 1)) mod 8)).

Definition c3_txt_ok (p : Z) : bool :=
  let s := c3_txt_s p in let sl := c3_txt_slack p in
  ro_bytes_b rsegs p (s ++ zb 0 :: sl) && negb (existsb (fun b => bz b =? 0) s) &&
  ((- (p + Z.of_nat (length s) + 1)) mod 8 <=? Z.of_nat (length sl)) &&
  (Z.of_nat (length s) <? 4096) && (65536 <=? p) && (p + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <=? 73728).

Lemma c3_texts_ok : forallb c3_txt_ok texts_ptrs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c3_nul_free : forall s : list byte, negb (existsb (fun b => bz b =? 0) s) = true -> ~ In (zb 0) s.
Proof.
  intros s H HI. apply negb_true_iff in H. assert (Hx : existsb (fun b => bz b =? 0) s = true).
  { apply existsb_exists. exists (zb 0). split; [exact HI | reflexivity]. }
  congruence.
Qed.

(* ==========================================================================
   3. Where the interface table's pointers point
   ========================================================================== *)

Lemma c3_link_ptr_class : forall i, (i < 64)%nat ->
  (exists k, 0 <= k < 64 /\ nth i link_ptrs 0 = A_G_NAMES + 8 * k) \/
  (exists j, (1 <= j < 6)%nat /\ nth i link_ptrs 0 = nth j odd_ptrs 0).
Proof.
  intros i Hi.
  assert (C : forallb (fun i => let q := nth i link_ptrs 0 in
                ((A_G_NAMES <=? q) && (q <? A_G_NAMES + 512) && ((q - A_G_NAMES) mod 8 =? 0)) ||
                existsb (fun j => q =? nth j odd_ptrs 0) (seq 1 5)) (seq 0 64) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C i (proj2 (in_seq 64 0 i) (conj (Nat.le_0_l i) Hi))).
  cbv zeta in C. apply orb_prop in C as [C|C].
  - left. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
    apply Z.leb_le in C1. apply Z.ltb_lt in C2. apply Z.eqb_eq in C3.
    exists ((nth i link_ptrs 0 - A_G_NAMES) / 8). split; [unfold A_G_NAMES in *; Z.div_mod_to_equations; lia|].
    Z.div_mod_to_equations. lia.
  - right. apply existsb_exists in C as (j & Hj & Hq). apply in_seq in Hj. apply Z.eqb_eq in Hq.
    exists j. split; [lia | exact Hq].
Qed.

Lemma c3_gname_nul_free : forall k, 0 <= k < 64 -> ~ In (zb 0) (gname k).
Proof.
  intros k Hk. apply c3_nul_free.
  assert (C : forallb (fun k => negb (existsb (fun b => bz b =? 0) (gname (Z.of_nat k)))) (seq 0 64) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. rewrite <- (Z2Nat.id k) by lia. apply C. apply in_seq. lia.
Qed.

(* the name an iftab_at entry names lies in g_names (at most 7 bytes, below long_alias) or in .rodata *)
Lemma c3_name_home : forall m kbs tab i nm ix p, iftab_at m kbs tab -> ifptrs_at m -> gnames_at m -> odd_at m ->
  nth_error tab i = Some (nm, ix) -> (i < 64)%nat ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> cstr_at m p nm ->
  p = nth i link_ptrs 0 /\ Z.of_nat (length nm) + 1 <= 12 /\
  ((A_G_NAMES <= p /\ p + Z.of_nat (length nm) + 1 <= A_LONG_ALIAS) \/
   (0x10000 <= p /\ p + Z.of_nat (length nm) + 1 <= 0x12000)).
Proof.
  intros m kbs tab i nm ix p HT HP HG HO Hn Hi Hu Hc.
  pose proof (c3_link_ptr_range i Hi) as Rq.
  assert (Ep : p = nth i link_ptrs 0)
    by (exact (c3_iftab_ptr m kbs tab i nm ix p _ HT Hn Hu (HP i Hi) ltac:(unfold A_G_NAMES, G_NAMES_SIZE in Rq; lia) Hc)).
  split; [exact Ep|]. subst p.
  destruct Hc as [Hcb Hcn].
  destruct (c3_link_ptr_class i Hi) as [(k & Hk & Eq) | (j & Hj & Eq)]; rewrite Eq in *.
  - destruct (HG k Hk) as (rest & HB & HL).
    pose proof (c3_cstr_uniq nm m _ (gname k) rest Hcb Hcn HB (c3_gname_nul_free k Hk)) as Enm. subst nm.
    rewrite length_app in HL. cbn [length] in HL.
    split; [lia|]. left. unfold A_LONG_ALIAS, A_G_NAMES. lia.
  - destruct (HO j ltac:(lia)) as [_ [HB HN]]. pose proof (c3_odd_home j ltac:(lia)) as Hh.
    pose proof (c3_cstr_uniq nm m _ (nth j odd_strs []) [] Hcb Hcn HB HN) as Enm. subst nm.
    split; [|right; lia].
    destruct j as [|[|[|[|[|[|j]]]]]]; cbn; lia.
Qed.

(* ==========================================================================
   4. kernel_c.v's Pre
   ========================================================================== *)

Lemma c3_kernel_pre : forall (E : lenv) (regs : bvmap 5 word) (m : word -> option byte) (kbs : list byte) (wp wn : word),
  lenv_ok E -> spZ regs = e_S E - SLOT_FRAME -> arg regs 0 = e_S E - SLOT_FRAME + FO_P ->
  rw_cells rsegs m (arg regs 0) [C8 wp; C8 wn] ->
  (exists d, bytes_at rsegs m (bv_unsigned wp) d /\ Z.of_nat (length d) = bv_unsigned wn) ->
  (bv_unsigned wp + bv_unsigned wn <= 0x10000 \/ 0x97000 <= bv_unsigned wp) ->
  bv_unsigned wp + bv_unsigned wn <= e_S E - SLOT_STACK_Z ->
  nlk_at m kbs -> nlk_wf kbs -> iftab_at m kbs link_tab -> ifptrs_at m -> texts_at m ->
  gnames_at m -> odd_at m -> la_ok m -> mem_inv rsegs m ->
  exists kbs (wp wn : word),
       nlk_at m kbs /\ frame_apart_gnl regs 4416 /\ nlk_wf kbs
       /\ rw_cells rsegs m (arg regs 0) [C8 wp; C8 wn]
       /\ apart_gnl (arg regs 0) 16 /\ apart_frame regs 4416 (arg regs 0) 16
       /\ (exists d, bytes_at rsegs m (bv_unsigned wp) d /\ Z.of_nat (length d) = bv_unsigned wn)
       /\ kernel_apart regs (bv_unsigned wp) (bv_unsigned wn)
       /\ kernel_apart regs A_TEXTS (8 * TEXTS_N)
       /\ (forall i, 0 <= i < TEXTS_N -> exists p s slack,
             u64_at m (A_TEXTS + 8 * i) p /\ p <> 0
             /\ bytes_at rsegs m p (s ++ zb 0 :: slack) /\ ~ In (zb 0) s
             /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
             /\ Z.of_nat (length s) < NL_CHUNK_MAX
             /\ kernel_apart regs p (Z.of_nat (length s) + 1 + Z.of_nat (length slack)))
       /\ (exists la sl,
             rw_cells rsegs m A_LONG_ALIAS [CB (Z.to_nat 300) la; C1 (zb 0)]
             /\ bytes_at rsegs m (A_LONG_ALIAS + LONG_ALIAS_SIZE) sl /\ length sl = 3%nat)
       /\ apart_frame regs 4416 A_LONG_ALIAS (LONG_ALIAS_SIZE + 3)
       /\ (arg regs 0 + 16 <= A_LONG_ALIAS \/ A_LONG_ALIAS + LONG_ALIAS_SIZE + 3 <= arg regs 0)
       /\ (forall tab i nm ix p, iftab_at m kbs tab -> nth_error tab i = Some (nm, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             kernel_apart regs p (Z.of_nat (length nm) + 1)).
Proof.
  intros E regs m kbs wp wn HE Hsp Ha0 HC Hd Hwimg Hwlo HK HKW HT HP HX HG HO HLA MI.
  destruct HE as (ES1 & ES2 & _).
  pose proof (bv_unsigned_in_range 64 wp) as Rwp. pose proof (bv_unsigned_in_range 64 wn) as Rwn.
  change (bv_modulus 64) with (2 ^ 64) in Rwp, Rwn.
  exists kbs, wp, wn.
  unfold frame_apart_gnl, kernel_apart. unfold apart_frame, apart_gnl. rewrite Hsp, Ha0.
  unfold SLOT_FRAME, SLOT_STACK_Z, FO_P, A_G_NL, NK_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE, A_TEXTS, TEXTS_N in *.
  split; [exact HK|]. split; [lia|]. split; [exact HKW|]. split; [rewrite <- Ha0; exact HC|].
  split; [lia|]. split; [lia|]. split; [exact Hd|].
  split; [repeat split; lia|]. split; [repeat split; lia|].
  split.
  { (* texts[] *)
    intros i Hi. set (p := nth (Z.to_nat i) texts_ptrs 0).
    exists p, (c3_txt_s p), (c3_txt_slack p).
    pose proof c3_texts_ok as C. rewrite forallb_forall in C.
    assert (Hin : In p texts_ptrs) by (unfold p; apply nth_In; cbn [length texts_ptrs]; lia).
    specialize (C p Hin). unfold c3_txt_ok in C. cbv zeta in C.
    apply andb_prop in C as [C C6]. apply andb_prop in C as [C C5]. apply andb_prop in C as [C C4].
    apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
    apply Z.leb_le in C6. apply Z.leb_le in C5. apply Z.ltb_lt in C4. apply Z.leb_le in C3.
    split.
    { pose proof (HX (Z.to_nat i) ltac:(lia)) as Hx. rewrite Z2Nat.id in Hx by lia. exact Hx. }
    split; [lia|].
    split.
    { apply (ro_bytes_at rsegs m p _ MI); [lia | rewrite length_app; cbn [length]; lia |].
      exact (ro_bytes_b_sound rsegs _ _ C1). }
    split; [exact (c3_nul_free _ C2)|].
    split; [exact C3|]. split; [unfold NL_CHUNK_MAX; exact C4|].
    repeat split; lia. }
  split; [exact HLA|].
  split; [lia|]. split; [lia|].
  (* the interface names *)
  intros tab i nm ix p HT' Hn Hu.
  assert (Hlen : length link_tab = 64%nat) by (vm_compute; reflexivity).
  assert (Hi : (i < 64)%nat).
  { destruct HT as (L1 & _ & _). destruct HT' as (L1' & _ & _).
    assert (Hs : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
    rewrite Hlen in L1. lia. }
  destruct HT' as (L1' & L2' & H3').
  destruct (H3' i nm ix Hn) as (_ & p' & Hu' & _ & Hc' & _).
  destruct (c3_name_home m kbs tab i nm ix p' (conj L1' (conj L2' H3')) HP HG HO Hn Hi Hu' Hc') as (Ep' & Hnm & Hhome).
  rewrite Ep' in Hhome.
  pose proof (c3_link_ptr_range i Hi) as Rq.
  set (q := nth i link_ptrs 0) in *.
  assert (Epq : Z_to_bv 64 p = Z_to_bv 64 q).
  { apply c3_le8_inj. unfold u64_at, wz in Hu, Hu'. rewrite Ep' in Hu'.
    exact (c3_bytes_at_same _ _ _ _ Hu Hu' ltac:(rewrite !length_le8; reflexivity)). }
  apply (f_equal bv_unsigned) in Epq. rewrite unsigned_lit_wrap, (unsigned_lit q) in Epq
    by (unfold A_G_NAMES, G_NAMES_SIZE in Rq; lia).
  clear - Epq Hnm Hhome Rq ES1 ES2. unfold A_G_NAMES, G_NAMES_SIZE, A_LONG_ALIAS in *.
  assert (Hc : p < 0 \/ 2 ^ 64 <= p \/ p = q).
  { destruct (Z_lt_dec p 0) as [H|H]; [left; exact H|]. destruct (Z_le_dec (2 ^ 64) p) as [H'|H']; [right; left; exact H'|].
    right; right. rewrite Z.mod_small in Epq by lia. exact Epq. }
  destruct Hc as [Hc|[Hc|Hc]].
  - assert (Hp : p <= q - 2 ^ 64) by (Z.div_mod_to_equations; nia).
    repeat split; lia.
  - repeat split; lia.
  - subst p. destruct Hhome as [Hh|Hh]; repeat split; lia.
Qed.
