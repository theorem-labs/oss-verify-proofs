(* Segment B2 of the op_write arm: what the interface table and the inlined name_of give the walk.
   Where each interface name lives (a g_names slot or a .rodata string), that the name the selector
   byte picks is a C string at the pointer the code passes, that index_of answers inside [0, 2 ^ 31),
   and the three disjointness facts the alias writer and index_of ask of every table name. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Frame Step Tac Bytes Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1B2Lib.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Lists
   ========================================================================== *)

Lemma c1b2_nth_of_error : forall (A : Type) (l : list A) i x d, nth_error l i = Some x -> nth i l d = x.
Proof.
  intros A l. induction l as [|y l IH]; intros i x d H.
  - destruct i; cbn in H; discriminate.
  - destruct i as [|i]; cbn in H |- *; [injection H as ->; reflexivity | apply IH; exact H].
Qed.

Lemma c1b2_error_lt : forall (A : Type) (l : list A) i x, nth_error l i = Some x -> (i < length l)%nat.
Proof.
  intros A l. induction l as [|y l IH]; intros i x H.
  - destruct i; cbn in H; discriminate.
  - destruct i as [|i]; cbn in H |- *; [lia | apply IH in H; lia].
Qed.

(* ==========================================================================
   2. The table's pointers and names
   ========================================================================== *)

Definition c1b2_nml (i : nat) : Z := Z.of_nat (length (fst (nth i link_tab (nil, 0)))).
Definition c1b2_ptr (i : nat) : Z := nth i link_ptrs 0.

Definition c1b2_pok (i : nat) : bool :=
  ((A_G_NAMES <=? c1b2_ptr i) && (c1b2_ptr i + c1b2_nml i + 1 <=? A_G_NAMES + G_NAMES_SIZE))
  || ((0x10000 <=? c1b2_ptr i) && (c1b2_ptr i + c1b2_nml i + 1 <=? 0x11eb4)).

Lemma c1b2_pok_all : forallb c1b2_pok (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c1b2_nml_all : forallb (fun i => c1b2_nml i <=? 11) (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c1b2_tab_len : length link_tab = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma c1b2_ptr_rng : forall i, (i < 64)%nat ->
  (A_G_NAMES <= c1b2_ptr i /\ c1b2_ptr i + c1b2_nml i + 1 <= A_G_NAMES + G_NAMES_SIZE)
  \/ (0x10000 <= c1b2_ptr i /\ c1b2_ptr i + c1b2_nml i + 1 <= 0x11eb4).
Proof.
  intros i Hi. pose proof c1b2_pok_all as H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)). unfold c1b2_pok in H.
  apply orb_true_iff in H. destruct H as [H|H]; apply andb_true_iff in H as [H1 H2];
    apply Z.leb_le in H1; apply Z.leb_le in H2; [left|right]; split; assumption.
Qed.

Lemma c1b2_nml_le : forall i, (i < 64)%nat -> 0 <= c1b2_nml i <= 11.
Proof.
  intros i Hi. pose proof c1b2_nml_all as H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)). apply Z.leb_le in H.
  unfold c1b2_nml in *. lia.
Qed.

Lemma c1b2_tab_nth : forall i nm ix, nth_error link_tab i = Some (nm, ix) ->
  (i < 64)%nat /\ c1b2_nml i = Z.of_nat (length nm).
Proof.
  intros i nm ix H. pose proof (c1b2_error_lt _ link_tab i (nm, ix) H) as Hi.
  rewrite c1b2_tab_len in Hi. split; [exact Hi|].
  unfold c1b2_nml. rewrite (c1b2_nth_of_error _ link_tab i (nm, ix) (nil, 0) H). reflexivity.
Qed.

(* ==========================================================================
   3. The odd table
   ========================================================================== *)

Definition c1b2_ook (i : nat) : bool :=
  (0x10000 <? nth i odd_ptrs 0)
  && (nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs nil)) + 1 <=? 0x11eb4).

Lemma c1b2_ook_all : forallb c1b2_ook (seq 0 6) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c1b2_odd_rng : forall i, (i < 6)%nat ->
  0x10000 < nth i odd_ptrs 0 /\
  nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs nil)) + 1 <= 0x11eb4.
Proof.
  intros i Hi. pose proof c1b2_ook_all as H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)). unfold c1b2_ook in H.
  apply andb_true_iff in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.leb_le in H2. split; assumption.
Qed.

(* ==========================================================================
   4. The names interfaces() writes into g_names
   ========================================================================== *)

Lemma c1b2_gname_len : forall k, 0 <= k < 64 -> (length (gname k) <= 4)%nat.
Proof.
  intros k Hk. unfold gname, gname_z. cbn [map length].
  unfold dec2. destruct (k <? 10); cbn [map length]; lia.
Qed.

Lemma c1b2_bz0 : bv_unsigned (zb 0) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma c1b2_byte0 : forall b : byte, bv_unsigned b = 0 -> b = zb 0.
Proof. intros b H. apply bv_eq. rewrite H, c1b2_bz0. reflexivity. Qed.

Lemma c1b2_gname_nonul : forall k, 0 <= k < 64 -> ~ In (zb 0) (gname k).
Proof.
  intros k Hk HIn. unfold gname in HIn. apply in_map_iff in HIn.
  destruct HIn as (v & Ev & Hv).
  assert (Hr : 1 <= v < 256).
  { unfold gname_z in Hv. destruct Hv as [<-|[<-|Hv]]; [lia|lia|].
    unfold dec2 in Hv. destruct (Z.ltb_spec k 10) as [Hl|Hl].
    - destruct Hv as [<-|[]]. lia.
    - destruct Hv as [<-|[<-|[]]]; Z.div_mod_to_equations; lia. }
  assert (E : bv_unsigned (zb v) = bv_unsigned (zb 0)) by (rewrite Ev; reflexivity).
  rewrite c1b2_bz0 in E. unfold zb in E. rewrite Z_to_bv_unsigned in E.
  unfold bv_wrap in E. change (bv_modulus 8) with 256 in E.
  rewrite Z.mod_small in E by lia. lia.
Qed.

(* ==========================================================================
   5. The selector byte: name_of, inlined
   ========================================================================== *)

Lemma c1b2_sel_rng : forall nb s, 0 <= nb < 256 -> sel_name nb = Some s ->
  (A_G_NAMES <= sel_ptr nb /\ sel_ptr nb + Z.of_nat (length s) + 1 <= A_G_NAMES + G_NAMES_SIZE)
  \/ (0x10000 <= sel_ptr nb /\ sel_ptr nb + Z.of_nat (length s) + 1 <= 0x11eb4).
Proof.
  intros nb s Hnb HS. unfold sel_name, sel_ptr in *.
  destruct (nb =? 255) eqn:E255; cbv beta iota in HS |- *; [discriminate HS|].
  destruct (nb <? 64) eqn:E64; cbv beta iota in HS |- *.
  - apply Z.ltb_lt in E64. left.
    replace s with (gname nb) by congruence.
    pose proof (c1b2_gname_len nb ltac:(lia)) as HL.
    unfold A_G_NAMES, G_NAMES_SIZE. lia.
  - right.
    remember (Z.to_nat (nb mod 6)) as j eqn:Ej.
    assert (Hj : (j < 6)%nat).
    { subst j. pose proof (Z.mod_pos_bound nb 6 ltac:(lia)). lia. }
    replace s with (nth j odd_strs nil) by congruence.
    pose proof (c1b2_odd_rng j Hj) as [R1 R2]. lia.
Qed.

Lemma c1b2_sel_ptr_rng : forall nb, 0 <= nb < 256 -> 0 <= sel_ptr nb < 2 ^ 31.
Proof.
  intros nb Hnb. unfold sel_ptr.
  destruct (nb =? 255) eqn:E255; cbv beta iota; [lia|].
  destruct (nb <? 64) eqn:E64; cbv beta iota.
  - apply Z.ltb_lt in E64. unfold A_G_NAMES. lia.
  - remember (Z.to_nat (nb mod 6)) as j eqn:Ej.
    assert (Hj : (j < 6)%nat).
    { subst j. pose proof (Z.mod_pos_bound nb 6 ltac:(lia)). lia. }
    pose proof (c1b2_odd_rng j Hj) as [R1 R2]. lia.
Qed.

Lemma c1b2_sel_str : forall m nb, 0 <= nb < 256 -> gnames_at m -> odd_at m ->
  str_arg m (sel_ptr nb) (sel_name nb).
Proof.
  intros m nb Hnb HG HO. unfold sel_name, sel_ptr.
  destruct (nb =? 255) eqn:E255; cbv beta iota; [reflexivity|].
  destruct (nb <? 64) eqn:E64; cbv beta iota.
  - apply Z.ltb_lt in E64.
    destruct (HG nb ltac:(lia)) as (rest & HB & HL).
    replace (gname nb ++ zb 0 :: rest) with ((gname nb ++ [zb 0]) ++ rest) in HB
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in HB. destruct HB as [HB _].
    split; [unfold A_G_NAMES; lia|].
    split; [exact HB | apply c1b2_gname_nonul; lia].
  - remember (Z.to_nat (nb mod 6)) as j eqn:Ej.
    assert (Hj : (j < 6)%nat).
    { subst j. pose proof (Z.mod_pos_bound nb 6 ltac:(lia)). lia. }
    destruct (HO j Hj) as [_ HC]. pose proof (c1b2_odd_rng j Hj) as [R1 R2].
    split; [lia | exact HC].
Qed.

(* ==========================================================================
   6. index_of answers inside [0, 2 ^ 31)
   ========================================================================== *)

Lemma c1b2_index_rng_gen : forall tab nm,
  (forall p, In p tab -> 0 <= snd p < 2 ^ 31) -> 0 <= index_of tab nm < 2 ^ 31.
Proof.
  intros tab nm H. induction tab as [|[n ix] tab IH]; cbn [index_of]; [lia|].
  destruct (bl_eqb n nm).
  - exact (H (n, ix) ltac:(left; reflexivity)).
  - apply IH. intros p Hp. apply H. right. exact Hp.
Qed.

Lemma c1b2_tab_ix : forallb (fun p => (0 <=? snd p) && (snd p <? 2 ^ 31)) link_tab = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c1b2_index_rng : forall nm, 0 <= index_of link_tab nm < 2 ^ 31.
Proof.
  intros nm. apply c1b2_index_rng_gen. intros p Hp.
  pose proof c1b2_tab_ix as H. rewrite forallb_forall in H. specialize (H p Hp).
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* ==========================================================================
   7. Each table name sits where the callees need it
   ========================================================================== *)

Lemma c1b2_iftab_ptr : forall m kbs i nm ix,
  ifptrs_at m -> iftab_at m kbs link_tab -> nth_error link_tab i = Some (nm, ix) ->
  (i < 64)%nat /\ u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) (c1b2_ptr i) /\
  cstr_at m (c1b2_ptr i) nm /\ u32_at m (A_G_NL + NK_IF_INDEX + 4 * Z.of_nat i) ix /\
  0 <= ix < 2 ^ 31.
Proof.
  intros m kbs i nm ix HP HT HE.
  destruct (c1b2_tab_nth i nm ix HE) as [Hi HN].
  destruct HT as (_ & _ & HT). destruct (HT i nm ix HE) as (Hix & p & HU & Hp0 & HC & HU32).
  pose proof (HP i Hi) as HQ.
  pose proof (c1b2_u64_same m _ p (c1b2_ptr i) HU HQ) as HM.
  pose proof (c1b2_ptr_rng i Hi) as HR. pose proof (c1b2_nml_le i Hi) as HL.
  assert (HQB : 0 <= c1b2_ptr i < 2 ^ 64).
  { unfold A_G_NAMES, G_NAMES_SIZE in HR. lia. }
  destruct HC as [HCB HCN].
  pose proof (bytes_at_bound rsegs m p (nm ++ [zb 0]) HCB) as HPB.
  rewrite length_app in HPB. cbn [length] in HPB.
  rewrite Z.mod_small in HM by lia. rewrite Z.mod_small in HM by lia.
  subst p. split; [exact Hi|]. split; [exact HQ|].
  split; [split; [exact HCB | exact HCN]|]. split; [exact HU32 | exact Hix].
Qed.

(* the three disjointness facts the alias writer (K = 16928) and index_of (K = 48) take of a
   table name: `p` is only known to read as the table's pointer, so it is that pointer, or it
   lies outside [0, 2 ^ 64) and misses every region by itself. *)
Lemma c1b2_ptr_apart : forall m kbs i nm ix p sp K,
  ifptrs_at m -> iftab_at m kbs link_tab -> nth_error link_tab i = Some (nm, ix) ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  480616 <= sp - K -> sp < 2 ^ 63 ->
  (p + (Z.of_nat (length nm) + 1) <= sp - K \/ sp <= p)
  /\ apart_gnl p (Z.of_nat (length nm) + 1)
  /\ apart A_ERRNO 4 p (Z.of_nat (length nm) + 1).
Proof.
  intros m kbs i nm ix p sp K HP HT HE HU Hsp Hsp2.
  destruct (c1b2_iftab_ptr m kbs i nm ix HP HT HE) as (Hi & HQ & _ & _ & _).
  destruct (c1b2_tab_nth i nm ix HE) as [_ HN].
  pose proof (c1b2_ptr_rng i Hi) as HR. pose proof (c1b2_nml_le i Hi) as HL.
  pose proof (c1b2_u64_same m _ p (c1b2_ptr i) HU HQ) as HM.
  assert (HQB : 0 <= c1b2_ptr i < 2 ^ 64).
  { unfold A_G_NAMES, G_NAMES_SIZE in HR. lia. }
  rewrite (Z.mod_small (c1b2_ptr i)) in HM by lia.
  unfold apart_gnl, apart, A_G_NL, NK_SIZE, A_G_NAMES, G_NAMES_SIZE, A_ERRNO, A_TP, ERRNO_TP_OFF in *.
  destruct (c1b2_mod_cases p (c1b2_ptr i) HM ltac:(lia)) as [->|[Hhi|Hlo]];
    repeat split; lia.
Qed.

(* the same three facts for the name the selector byte picks *)
Lemma c1b2_sel_apart : forall nb s sp K,
  0 <= nb < 256 -> sel_name nb = Some s -> 480616 <= sp - K -> sp < 2 ^ 63 ->
  (sel_ptr nb + (Z.of_nat (length s) + 1) <= sp - K \/ sp <= sel_ptr nb)
  /\ apart_gnl (sel_ptr nb) (Z.of_nat (length s) + 1).
Proof.
  intros nb s sp K Hnb HS Hsp Hsp2.
  pose proof (c1b2_sel_rng nb s Hnb HS) as HR.
  unfold apart_gnl, A_G_NL, NK_SIZE, A_G_NAMES, G_NAMES_SIZE in *.
  split; lia.
Qed.

(* ==========================================================================
   8. The first byte of a C string
   ========================================================================== *)

Lemma c1b2_first_byte : forall m p s, cstr_at m p s ->
  exists b, ov_read_bytes rsegs m (wa p) 1 = Some [b] /\ (bv_unsigned b = 0 <-> s = []).
Proof.
  intros m p s [HB HN]. destruct s as [|b s'].
  - cbn [app] in HB. exists (zb 0). split; [exact (c1b2_read1 m p (zb 0) [] HB)|].
    split; [reflexivity | intros _; exact c1b2_bz0].
  - cbn [app] in HB. exists b. split; [exact (c1b2_read1 m p b (s' ++ [zb 0]) HB)|].
    split; [intros H0 | intros H0; discriminate H0].
    exfalso. apply HN. left. exact (c1b2_byte0 b H0).
Qed.
