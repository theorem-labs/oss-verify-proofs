(* reac_link_alias_read (reac_link_alias.c:95-119), PLAIN build: the walk of its contract
   (lib/Prog/reac_link_alias_read_c.v) on the plain image, 56 instructions at 0x15f2c.

   Frame 80: ra s0-s4 at sp0-8 .. sp0-48, the 32-byte request at [sp0-80, sp0-48).
   The two guarded NUL stores (0x15f60, 0x15f6c), the -EINVAL refusals (0x15f74, 0x15f7c),
   fuzz_if_nametoindex (0x15f80; -ENODEV at 0x15fe0), memset of the request tail (0x15f98), the
   four header stores (0x15fac .. 0x15fb8, which with the memset make `req_read idx`), and
   nl_talk (0x15fd4). The three callees are hypotheses: their contracts (index_of_c.v,
   memset_c.v, nl_talk_c.v), proved by other lanes. Every instruction is decoded from the image
   at its own address by `zstep`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call mk_str mk_marks
  reac_link_alias_read_c nl_talk_c index_of_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Memory facts
   ========================================================================== *)

Lemma wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2) <-> wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). split; [split; [lia|]; split; [lia|]; intros i Hi; apply H; lia|].
    split; [lia|]. split; [lia|]. intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H; lia.
  - intros [(Ha & Hl & H) (Hb & Hl2 & H')]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i n1); [apply H; lia|].
    replace (A + i) with (A + n1 + (i - n1)) by lia. apply H'; lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] [R1 R2]]. rewrite cells_bytes_length in B2 by exact W1. tauto.
  - intros [[[W1 B1] R1] [[W2 B2] R2]]. rewrite cells_bytes_length by exact W1. tauto.
Qed.

(* a CB cell cut in two *)
Lemma rw_cells_cut : forall m A n1 n2 junk, rw_cells rsegs m A [CB (n1 + n2) junk] ->
  exists j1 j2, rw_cells rsegs m A [CB n1 j1] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB n2 j2].
Proof.
  intros m A n1 n2 junk H.
  pose proof (rw_cells_split_CB rsegs m A [] (n1 + n2) junk [] [n1; n2] H ltac:(cbn; lia)) as H'.
  cbn [app mk_CB_cells] in H'.
  change [CB n1 (firstn n1 junk); CB n2 (firstn n2 (skipn n1 junk))]
    with ([CB n1 (firstn n1 junk)] ++ [CB n2 (firstn n2 (skipn n1 junk))]) in H'.
  apply rw_cells_app in H'. destruct H' as [H1 H2]. cbn [cells_size csize] in H2.
  rewrite Nat.add_0_r in H2. eauto.
Qed.

Lemma rw_cells_join : forall m A c cs, rw_cells rsegs m A [c] ->
  rw_cells rsegs m (A + Z.of_nat (csize c)) cs -> rw_cells rsegs m A (c :: cs).
Proof.
  intros m A c cs H1 H2. change (c :: cs) with ([c] ++ cs). apply rw_cells_app. split; [exact H1|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ B] _]. exact B. Qed.

Lemma munch_sym : forall W m m', munch W m m' -> munch W m' m.
Proof. intros W m m' H x Hx. symmetry. apply H, Hx. Qed.

Lemma rw_cells_c1_cb : forall m A b n j, rw_cells rsegs m A [C1 b] -> rw_cells rsegs m (A + 1) [CB n j] ->
  rw_cells rsegs m A [CB (S n) (b :: j)].
Proof.
  intros m A b n j H1 H2. pose proof (rw_cells_join m A (C1 b) [CB n j] H1 H2) as H.
  pose proof (rw_cells_merge rsegs m A [] [C1 b; CB n j] [] H) as H'.
  cbn [app cells_size cells_bytes csize cbytes] in H'. rewrite Nat.add_0_r, app_nil_r in H'. exact H'.
Qed.

(* An object is clear of a write window when none of its bytes is inside it. Unlike
   `disjoint_from`, an empty window (a NULL buffer, or a zero cap) is clear of everything. *)
Definition clear_of (W : list ivl) (a n : Z) : Prop := forall x, a <= x < a + n -> outside W x.

Ltac clear_tac := unfold clear_of; intros ? ?; cbn [outside]; repeat apply conj; try exact I; lia.

Lemma clear_sub : forall W W' a n, clear_of W a n -> sub_fp W' W -> clear_of W' a n.
Proof. intros W W' a n C S x Hx. apply S, C, Hx. Qed.

Lemma bytes_at_move : forall W m m' a bs, bytes_at rsegs m a bs -> munch W m m' ->
  clear_of W a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (Ha & Hl & H) MU C. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd. rewrite (MU (wa (a + Z.of_nat i))); [reflexivity|].
  rewrite wa_unsigned by lia. apply C. lia.
Qed.

Lemma u8arr_move : forall W m m' a bs, u8arr rsegs m a bs -> munch W m m' -> wmono rsegs m m' ->
  clear_of W a (Z.of_nat (length bs)) -> u8arr rsegs m' a bs.
Proof.
  intros W m m' a bs [B R] MU WM C.
  split; [exact (bytes_at_move W m m' a bs B MU C) | exact (wr_at_transport rsegs m m' _ _ R WM)].
Qed.

Lemma rw_cells_move : forall W m m' a cs, rw_cells rsegs m a cs -> munch W m m' -> wmono rsegs m m' ->
  clear_of W a (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' a cs.
Proof.
  intros W m m' a cs [[Wf B] R] MU WM C.
  split; [split; [exact Wf|] | exact (wr_at_transport rsegs m m' _ _ R WM)].
  apply (bytes_at_move W m m' a _ B MU). rewrite cells_bytes_length by exact Wf. exact C.
Qed.

Lemma cstr_move : forall W m m' a s, cstr_at m a s -> munch W m m' ->
  clear_of W a (Z.of_nat (length s) + 1) -> cstr_at m' a s.
Proof.
  intros W m m' a s [B N] MU C. split; [|exact N]. apply (bytes_at_move W m m' a _ B MU).
  rewrite length_app. cbn [length]. replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) by lia.
  exact C.
Qed.

Lemma u64_back : forall W m m' a p, munch W m m' -> clear_of W a 8 -> u64_at m' a p -> u64_at m a p.
Proof.
  intros W m m' a p MU C H. unfold u64_at in *.
  apply (bytes_at_move W m' m a _ H (munch_sym _ _ _ MU)). rewrite length_le8. exact C.
Qed.

Lemma nlk_move : forall W m m' bs, nlk_at m bs -> munch W m m' -> wmono rsegs m m' ->
  clear_of W A_G_NL NK_SIZE -> nlk_at m' bs.
Proof.
  intros W m m' bs [U L] MU WM C. split; [|exact L]. apply (u8arr_move W m m' _ _ U MU WM). rewrite L. exact C.
Qed.

Lemma iftab_keep : forall W m m' bs bs' tab,
  iftab_at m bs tab -> munch W m m' -> nk_n_if bs' = nk_n_if bs ->
  (forall i, (i < length tab)%nat ->
     clear_of W (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) 8 /\
     clear_of W (A_G_NL + NK_IF_INDEX + 4 * Z.of_nat i) 4) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> clear_of W p (Z.of_nat (length n2) + 1)) ->
  iftab_at m' bs' tab.
Proof.
  intros W m m' bs bs' tab (L & L80 & E) MU Hn DS DN.
  split; [lia|]. split; [exact L80|]. intros i n2 ix Hi.
  destruct (E i n2 ix Hi) as (R & p & P & Pz & C & I). split; [exact R|].
  assert (Li : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  destruct (DS i Li) as [D1 D2].
  exists p. split; [|split; [exact Pz|split]].
  - unfold u64_at in *. apply (bytes_at_move W m m' _ _ P MU). rewrite length_le8. exact D1.
  - exact (cstr_move W m m' p n2 C MU (DN i n2 ix p Hi P)).
  - unfold u32_at in *. apply (bytes_at_move W m m' _ _ I MU). rewrite length_le4. exact D2.
Qed.

(* a buffer the function emptied: its first byte is the NUL, and it is still the caller's buffer *)
Definition bufz (m : word -> option byte) (p n : Z) : Prop :=
  p <> 0 -> 1 <= n -> cstr_at m p [] /\ exists junk, rw_cells rsegs m p [CB (Z.to_nat n) junk].

Lemma bufz_move : forall W m m' p n, bufz m p n -> munch W m m' -> wmono rsegs m m' ->
  (p <> 0 -> 1 <= n -> clear_of W p n) -> bufz m' p n.
Proof.
  intros W m m' p n B MU WM C Hp Hn. destruct (B Hp Hn) as [Cs (j & R)]. specialize (C Hp Hn).
  split.
  - apply (cstr_move W m m' p [] Cs MU). intros x Hx. apply C. cbn in Hx. lia.
  - exists j. apply (rw_cells_move W m m' p _ R MU WM). cbn [cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by lia. exact C.
Qed.

(* a write window (p, p + (if p =? 0 then 0 else c)) is empty, or apart from an object the
   Pre keeps apart from a real buffer *)
Lemma cond_apart : forall a n p c, 0 <= c -> (p <> 0 -> 1 <= c -> apart a n p c) ->
  (if p =? 0 then 0 else c) = 0 \/ apart a n p (if p =? 0 then 0 else c).
Proof.
  intros a n p c Hc H. destruct (Z.eqb_spec p 0) as [E|E]; [left; reflexivity|].
  destruct (Z.eq_dec c 0) as [->|Hc0]; [left; reflexivity|]. right. apply H; lia.
Qed.

Lemma apart_sym : forall a n b k, apart a n b k -> apart b k a n.
Proof. unfold apart. lia. Qed.

(* a disjunction kept out of every `lia` call of the walk until a step unfolds it: `lia`
   case-splits each disjunction in its context *)
Definition hold (P : Prop) : Prop := P.

Ltac curmem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mp _) => mp end.

(* `sb zero, 0(p)` through a register that holds the word `p` itself: the kit's store tactic
   wants the address as a literal or `wa`, so the store is taken through a `store_ok` fact and
   the written memory is put back in `wa` form for `mem_after_store`. *)
Ltac nul_store B1 p :=
  let mp := curmem in
  let HS := fresh "HS" in
  assert (HS : store_ok rsegs mp p 1 = true)
    by (eapply (rw_cells_store_ok_at rsegs mp (bv_unsigned p) _ 0 _ 1 p B1); try reflexivity;
        unfold wa; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned);
  zstep;
  replace (write_to_mem mp p (le1 (Z_to_bv 64 0))) with (write_to_mem mp (wa (bv_unsigned p + Z.of_nat 0)) [Z_to_bv 8 0])
    by (f_equal; try reflexivity; unfold wa; change (Z.of_nat 0) with 0; rewrite Z.add_0_r;
        apply Z_to_bv_bv_unsigned);
  clear HS; mem_after_store.

(* ==========================================================================
   2. Uniqueness: the Post quantifies afresh over the kernel bytes, the table and the name
   ========================================================================== *)

Lemma nlk_at_unique : forall m b1 b2, nlk_at m b1 -> nlk_at m b2 -> b1 = b2.
Proof.
  intros m b1 b2 [[B1 _] L1] [[B2 _] L2]. apply (bytes_at_unique m A_G_NL); [exact B1 | exact B2 | lia].
Qed.

Lemma u64_at_unique : forall m a p1 p2, u64_at m a p1 -> u64_at m a p2 -> wz p1 = wz p2.
Proof.
  intros m a p1 p2 H1 H2. unfold u64_at in *.
  pose proof (bytes_at_unique m a _ _ H1 H2 ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 (wz p1)), <- (le_bytes_to_word_le8 (wz p2)), E. reflexivity.
Qed.

Lemma u32_at_small_unique : forall m a x1 x2, u32_at m a x1 -> u32_at m a x2 ->
  0 <= x1 < 2 ^ 31 -> 0 <= x2 < 2 ^ 31 -> x1 = x2.
Proof.
  intros m a x1 x2 H1 H2 R1 R2. unfold u32_at in *.
  pose proof (bytes_at_unique m a _ _ H1 H2 ltac:(rewrite !length_le4; reflexivity)) as E.
  apply (f_equal bytes_le_to_Z) in E. rewrite !bytes_le_to_Z_le4 in E. unfold wz in E.
  rewrite !unsigned_lit in E by lia. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma cstr_at_range : forall m p s, cstr_at m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof. intros m p s [B _]. apply bytes_at_bound in B. rewrite length_app in B. cbn [length] in B. lia. Qed.

Lemma iftab_unique : forall m bs tab1 tab2, iftab_at m bs tab1 -> iftab_at m bs tab2 -> tab1 = tab2.
Proof.
  intros m bs tab1 tab2 (L1 & _ & E1) (L2 & _ & E2).
  assert (L : length tab1 = length tab2) by lia.
  apply nth_error_ext. intros i.
  destruct (nth_error tab1 i) as [[n1 x1]|] eqn:H1; destruct (nth_error tab2 i) as [[n2 x2]|] eqn:H2.
  - destruct (E1 i n1 x1 H1) as (R1 & p1 & P1 & _ & C1 & I1).
    destruct (E2 i n2 x2 H2) as (R2 & p2 & P2 & _ & C2 & I2).
    pose proof (u64_at_unique _ _ _ _ P1 P2) as Ep.
    pose proof (cstr_at_range _ _ _ C1). pose proof (cstr_at_range _ _ _ C2).
    assert (p1 = p2) by (unfold wz in Ep; apply (f_equal bv_unsigned) in Ep;
                         rewrite !unsigned_lit in Ep by lia; exact Ep).
    subst p2. rewrite (cstr_at_unique m n1 p1 n2 C1 C2).
    rewrite (u32_at_small_unique _ _ _ _ I1 I2 R1 R2). reflexivity.
  - exfalso. apply nth_error_None in H2. assert (i < length tab1)%nat by (apply nth_error_Some; congruence). lia.
  - exfalso. apply nth_error_None in H1. assert (i < length tab2)%nat by (apply nth_error_Some; congruence). lia.
  - reflexivity.
Qed.

(* ==========================================================================
   3. Pure facts of the model
   ========================================================================== *)

Lemma index_of_range : forall tab s, (forall i n ix, nth_error tab i = Some (n, ix) -> 0 <= ix < 2 ^ 31) ->
  0 <= index_of tab s < 2 ^ 31.
Proof.
  induction tab as [|[n ix] tab IH]; intros s H; cbn [index_of]; [lia|].
  destruct (bl_eqb n s).
  - exact (H 0%nat n ix eq_refl).
  - apply IH. intros i n2 ix2 E. exact (H (S i) n2 ix2 E).
Qed.

Lemma talk_after_sock : forall K, k_sock (talk_after K) = 0.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [reflexivity|].
  destruct (negb (k_send K =? 0)); [reflexivity|].
  destruct (chunk_loop _ _ _) as [v j]. destruct v; reflexivity.
Qed.

Lemma nk_sent_length : forall bs, 0 <= nk_n_sent bs -> Z.of_nat (length (nk_sent bs)) = nk_n_sent bs.
Proof. intros bs H. unfold nk_sent. rewrite length_map, length_seq. lia. Qed.

(* ==========================================================================
   4. The contract's three parts, and the two shapes of its Post
   ========================================================================== *)

Definition rd_pre := ltac:(let c := eval cbv delta [reac_link_alias_read_contract] in reac_link_alias_read_contract in
  lazymatch c with leaf _ _ ?P _ _ => exact P end).
Definition rd_wr := ltac:(let c := eval cbv delta [reac_link_alias_read_contract] in reac_link_alias_read_contract in
  lazymatch c with leaf _ _ _ ?W _ => exact W end).
Definition rd_post := ltac:(let c := eval cbv delta [reac_link_alias_read_contract] in reac_link_alias_read_contract in
  lazymatch c with leaf _ _ _ _ ?Q => exact Q end).

Lemma rd_contract_eq : reac_link_alias_read_contract = leaf REAC_LINK_ALIAS_READ 16672 rd_pre rd_wr rd_post.
Proof. reflexivity. Qed.


Lemma rd_post_refuse : forall regs mI regs' m' kbs tab nm rc,
  nlk_at mI kbs -> iftab_at mI kbs tab -> str_arg mI (arg regs 0) nm -> nlk_wf kbs -> nk_open kbs = 0 ->
  read_lib tab nm (arg regs 2) (arg regs 4) (nk_sent kbs) (nk_kstate kbs)
    = Rres rc [] [] (nk_sent kbs) (nk_kstate kbs) ->
  getr regs' 10 = wz rc ->
  nlk_at m' kbs -> iftab_at m' kbs tab ->
  bufz m' (arg regs 1) (arg regs 2) -> bufz m' (arg regs 3) (arg regs 4) ->
  rd_post regs mI regs' m'.
Proof.
  intros regs mI regs' m' kbs tab nm rc NK IT SN WF OP ER RC NK' IT' BK BA.
  intros kbs2 tab2 nm2 NK2 IT2 SN2.
  assert (kbs2 = kbs) by exact (nlk_at_unique _ _ _ NK2 NK). subst kbs2.
  assert (tab2 = tab) by exact (iftab_unique _ _ _ _ IT2 IT). subst tab2.
  assert (nm2 = nm) by exact (str_arg_unique _ _ _ _ SN2 SN). subst nm2.
  cbv zeta. rewrite ER. cbn [r_rc r_kind r_alias r_reqs r_state].
  pose proof WF as WF'. destruct WF' as (W1 & W2 & W3 & _).
  split; [exact RC|].
  split.
  - exists kbs. split; [exact NK'|]. split; [exact WF|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact IT'|].
    split; [cbn [k_next nk_kstate]; lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [symmetry; apply nk_sent_length; lia|].
    split; [exact OP|split; [reflexivity|split; [reflexivity|split; [lia|intros _; reflexivity]]]].
  - split; [intros H1 H2; exact (proj1 (BK H1 H2))|].
    split; [intros H1 H2; exact (proj1 (BA H1 H2))|].
    split; [intros H1 H2; exact (proj2 (BK H1 H2))|].
    intros H1 H2; exact (proj2 (BA H1 H2)).
Qed.

Lemma rd_post_talk : forall regs mI regs' m' kbs tab s,
  nlk_at mI kbs -> iftab_at mI kbs tab -> str_arg mI (arg regs 0) (Some s) -> nlk_wf kbs ->
  s <> [] -> index_of tab s <> 0 ->
  getr regs' 10 = wz (talk_rc_lib (nk_kstate kbs)) ->
  (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
       /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
       /\ nk_n_if kbs' = nk_n_if kbs
       /\ nk_socket_errno kbs' = 0
       /\ nk_send_errno kbs' = k_send (talk_after (nk_kstate kbs))
       /\ nk_next kbs' = Z.of_nat (k_next (talk_after (nk_kstate kbs)))
       /\ nk_sent kbs' = (if talk_owes (nk_kstate kbs) then owe (nk_sent kbs) (req_read (index_of tab s))
                          else nk_sent kbs)
       /\ nk_n_sent kbs' = Z.of_nat (length (nk_sent kbs'))
       /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
       /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
       /\ (nk_socket_errno kbs <> 0 -> nk_opened kbs' = nk_opened kbs)
       /\ (nk_socket_errno kbs = 0 -> nk_opened kbs' = nk_opened kbs + 1)) ->
  (forall bs', nk_n_if bs' = nk_n_if kbs -> iftab_at m' bs' tab) ->
  (forall pay, a_kind (talk_attrs (nk_kstate kbs)) = Some pay -> arg regs 1 <> 0 -> 1 <= arg regs 2 ->
     cstr_at m' (arg regs 1) (cut_text pay (arg regs 2))) ->
  (forall pay, a_alias (talk_attrs (nk_kstate kbs)) = Some pay -> arg regs 3 <> 0 -> 1 <= arg regs 4 ->
     cstr_at m' (arg regs 3) (cut_text pay (arg regs 4))) ->
  (a_kind (talk_attrs (nk_kstate kbs)) = None -> arg regs 1 <> 0 -> 1 <= arg regs 2 -> cstr_at m' (arg regs 1) []) ->
  (a_alias (talk_attrs (nk_kstate kbs)) = None -> arg regs 3 <> 0 -> 1 <= arg regs 4 -> cstr_at m' (arg regs 3) []) ->
  (arg regs 1 <> 0 -> 1 <= arg regs 2 -> exists junk, rw_cells rsegs m' (arg regs 1) [CB (Z.to_nat (arg regs 2)) junk]) ->
  (arg regs 3 <> 0 -> 1 <= arg regs 4 -> exists junk, rw_cells rsegs m' (arg regs 3) [CB (Z.to_nat (arg regs 4)) junk]) ->
  rd_post regs mI regs' m'.
Proof.
  intros regs mI regs' m' kbs tab s NK IT SN WF Sne Inz RC NL IT' KS AS KN AN KR AR.
  intros kbs2 tab2 nm2 NK2 IT2 SN2.
  assert (kbs2 = kbs) by exact (nlk_at_unique _ _ _ NK2 NK). subst kbs2.
  assert (tab2 = tab) by exact (iftab_unique _ _ _ _ IT2 IT). subst tab2.
  assert (nm2 = Some s) by exact (str_arg_unique _ _ _ _ SN2 SN). subst nm2.
  cbv zeta. unfold read_lib, read_core.
  replace (Nat.eqb (length s) 0) with false by (destruct s; [contradiction | reflexivity]).
  replace (index_of tab s =? 0) with false by (symmetry; apply Z.eqb_neq; exact Inz).
  cbn [r_rc r_kind r_alias r_reqs r_state].
  split; [exact RC|].
  split.
  - destruct NL as (kbs' & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
    exists kbs'. split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|].
    split; [exact N5|]. split; [apply IT'; exact N5|]. split; [exact N8|].
    split; [rewrite talk_after_sock; exact N6|]. split; [exact N7|]. split; [exact N9|].
    split; [rewrite N10, N9; reflexivity|]. split; [exact N11|]. split; [exact N12|]. split; [exact N13|].
    split; [destruct (Z.eq_dec (nk_socket_errno kbs) 0) as [E|E]; [rewrite (N15 E) | rewrite (N14 E)]; lia|].
    intros [H|[H|H]]; [discriminate | injection H as ->; contradiction | exfalso; exact (Inz (H s eq_refl))].
  - assert (KC : forall c, 1 <= c -> (c <? 1) = false) by (intros c Hc; apply Z.ltb_ge; lia).
    split; [intros H1 H2; rewrite (KC _ H2); unfold text_of_attr;
            destruct (a_kind (talk_attrs (nk_kstate kbs))) as [pay|];
            [exact (KS pay eq_refl H1 H2) | exact (KN eq_refl H1 H2)]|].
    split; [intros H1 H2; rewrite (KC _ H2); unfold text_of_attr;
            destruct (a_alias (talk_attrs (nk_kstate kbs))) as [pay|];
            [exact (AS pay eq_refl H1 H2) | exact (AN eq_refl H1 H2)]|].
    split; [exact KR | exact AR].
Qed.

(* the 32 bytes the four header stores and the memset leave at sp: `req_read idx` *)
Lemma req_cells : forall idx (v0 v1 v2 v3 : word) j1 j2, 0 <= idx < 2 ^ 31 ->
  v0 = Z_to_bv 64 32 -> v1 = Z_to_bv 64 65554 -> v2 = Z_to_bv 64 1 -> v3 = Z_to_bv 64 idx ->
  j1 = zeros 8 -> j2 = zeros 8 ->
  cells_bytes [C4 v0; C4 v1; C4 v2] ++ cells_bytes [CB 8 j1; C4 v3; CB 8 j2] = req_read idx.
Proof.
  assert (BE : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2).
  { induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
    injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2]. }
  intros idx v0 v1 v2 v3 j1 j2 R -> -> -> -> -> ->. cbn [cells_bytes cbytes]. unfold le4.
  rewrite !unsigned_lit by lia. unfold req_read, req_head.
  replace (Z_to_le_bytes 4 65554) with (Z_to_le_bytes 2 RTM_GETLINK ++ Z_to_le_bytes 2 F_REQUEST)
    by (apply BE; vm_compute; reflexivity).
  change (zeros (32 - 24)) with (zeros 8).
  replace (zeros 8) with (zeros 4 ++ zeros 4) by reflexivity.
  rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

(* ==========================================================================
   5. The walk
   ========================================================================== *)

Theorem reac_link_alias_read_holds : fuzz_if_nametoindex_contract -> memset_contract -> nl_talk_contract ->
  reac_link_alias_read_contract.
Proof.
  intros HIX HMS HNT. rewrite rd_contract_eq. apply leaf_intro.
  - intros r1 r2 m E H. unfold rd_pre, frame_apart_gnl, apart_frame, arg, errno_at, spZ in *.
    rewrite <- !E. exact H.
  - intros r1 r2 m E. unfold rd_wr, arg, errno_at. rewrite !E. reflexivity.
  - intros r1 r2 m q1 q2 m' E1 E2 H. unfold rd_post, arg in *. rewrite <- !E1, <- !E2. exact H.
  - unfold leaf_walk, REAC_LINK_ALIAS_READ, rd_wr.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta beta. intros HP MI ST LO SP. unfold rd_pre in HP. cbv beta in HP.
    destruct HP as (kbs & tab & nm & NK & FG & WF & OP & OPN & CLN & IT & ER & EF & EG & SN & BK & BA & TN & NA & KA
            & KE & AE & NF & KF & AF).
    rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_errno, ?mkR_ra in *.
    unfold frame_apart_gnl in FG. rewrite mkR_sp in FG.
    assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
    pose proof (zr_word sp) as Rsp. pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1.
    pose proof (zr_word a2) as Ra2. pose proof (zr_word a3) as Ra3. pose proof (zr_word a4) as Ra4.
    pose proof (zr_word tp) as Rtp. unfold inr64 in Rsp, Ra0, Ra1, Ra2, Ra3, Ra4, Rtp.
    assert (HG : A_G_NL = 203648) by reflexivity. assert (HNS : NK_SIZE = 271992) by reflexivity.
    assert (HNN : NK_N_SENT = 271016) by reflexivity. assert (HEO : ERRNO_TP_OFF = -164) by reflexivity.
    assert (HIN : NK_IF_NAME = 271024) by reflexivity. assert (HII : NK_IF_INDEX = 271664) by reflexivity.
    (* the two buffer windows, against the frame and against g_nl *)
    assert (KFW : hold (bv_unsigned a1 + (if bv_unsigned a1 =? 0 then 0 else bv_unsigned a2) <= bv_unsigned sp - 16672
                        \/ bv_unsigned sp <= bv_unsigned a1)).
    { unfold hold. destruct (Z.eqb_spec (bv_unsigned a1) 0) as [E|E]; cbv iota; [lia|].
      destruct (KF E) as [H _]. unfold apart_frame in H. rewrite mkR_sp in H. lia. }
    assert (AFW : hold (bv_unsigned a3 + (if bv_unsigned a3 =? 0 then 0 else bv_unsigned a4) <= bv_unsigned sp - 16672
                        \/ bv_unsigned sp <= bv_unsigned a3)).
    { unfold hold. destruct (Z.eqb_spec (bv_unsigned a3) 0) as [E|E]; cbv iota; [lia|].
      destruct (AF E) as [H _]. unfold apart_frame in H. rewrite mkR_sp in H. lia. }
    assert (KGW : hold (bv_unsigned a1 + (if bv_unsigned a1 =? 0 then 0 else bv_unsigned a2) <= A_G_NL
                        \/ A_G_NL + NK_SIZE <= bv_unsigned a1)).
    { unfold hold. destruct (Z.eqb_spec (bv_unsigned a1) 0) as [E|E]; cbv iota; [lia|].
      destruct (KF E) as [_ H]. unfold apart_gnl in H. lia. }
    assert (AGW : hold (bv_unsigned a3 + (if bv_unsigned a3 =? 0 then 0 else bv_unsigned a4) <= A_G_NL
                        \/ A_G_NL + NK_SIZE <= bv_unsigned a3)).
    { unfold hold. destruct (Z.eqb_spec (bv_unsigned a3) 0) as [E|E]; cbv iota; [lia|].
      destruct (AF E) as [_ H]. unfold apart_gnl in H. lia. }
    assert (ER0 : wr_at rsegs m (bv_unsigned tp + ERRNO_TP_OFF) 4 /\ True) by (split; [exact ER | exact I]).
    clear ER.
    pose proof (munch_refl [(bv_unsigned sp - 16672, bv_unsigned sp); (A_G_NL, A_G_NL + NK_N_SENT + 4);
       (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4);
       (bv_unsigned a1, bv_unsigned a1 + (if bv_unsigned a1 =? 0 then 0 else bv_unsigned a2));
       (bv_unsigned a3, bv_unsigned a3 + (if bv_unsigned a3 =? 0 then 0 else bv_unsigned a4))] m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 16672, bv_unsigned sp);
       (bv_unsigned a1, bv_unsigned a1 + (if bv_unsigned a1 =? 0 then 0 else bv_unsigned a2));
       (bv_unsigned a3, bv_unsigned a3 + (if bv_unsigned a3 =? 0 then 0 else bv_unsigned a4))] m) as MT.
    pose proof (munch_refl [(bv_unsigned sp - 16672, bv_unsigned sp);
       (bv_unsigned a1, bv_unsigned a1 + (if bv_unsigned a1 =? 0 then 0 else bv_unsigned a2))] m) as MK.
    pose proof (munch_refl [(bv_unsigned sp - 16672, bv_unsigned sp)] m) as M0.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 80%nat ST.
    do 11 zstep.
    (* 0x15f58: the two NUL stores, then (REST) from 0x15f70 *)
    lazymatch goal with |- evt _ ?Q (MS ?R _ _ _ _ _ _) =>
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
    lazymatch type of MU with munch ?W _ _ =>
    lazymatch type of MT with munch ?Wt _ _ =>
    lazymatch type of MK with munch ?Wk _ _ =>
      assert (REST : forall m2, rw_cells rsegs m2 (bv_unsigned sp + -80) cs -> stk rsegs m2 lo (bv_unsigned sp + -80) ->
                munch W m m2 -> munch Wt m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
                bufz m2 (bv_unsigned a1) (bv_unsigned a2) -> bufz m2 (bv_unsigned a3) (bv_unsigned a4) ->
                evt rsegs Q (MS R F (Z_to_bv 64 89968) fc None m2 (seg_rom rsegs)));
      [ | assert (MID : forall m2, rw_cells rsegs m2 (bv_unsigned sp + -80) cs -> stk rsegs m2 lo (bv_unsigned sp + -80) ->
                munch W m m2 -> munch Wt m m2 -> munch Wk m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
                bufz m2 (bv_unsigned a1) (bv_unsigned a2) ->
                evt rsegs Q (MS R F (Z_to_bv 64 89956) fc None m2 (seg_rom rsegs))) ]
    end end end end end.
    { (* ---------------- REST: from 0x15f70 ---------------- *)
      intros m2 FR2 ST2 MU2 MT2 WM2 MI2 KZ AZ.
      clear FR ST MU MT MK M0 WM MI.
      rename FR2 into FR, ST2 into ST, MU2 into MU, MT2 into MT, WM2 into WM, MI2 into MI.
      pose proof (munch_refl [(bv_unsigned sp - 16672, bv_unsigned sp)] m2) as MF.
      pose proof (wmono_refl rsegs m2) as WF2.
      (* g_nl, the table and the buffers, at any later memory *)
      assert (NKk : forall mx, munch [(bv_unsigned sp - 16672, bv_unsigned sp);
                      (bv_unsigned a1, bv_unsigned a1 + (if bv_unsigned a1 =? 0 then 0 else bv_unsigned a2));
                      (bv_unsigned a3, bv_unsigned a3 + (if bv_unsigned a3 =? 0 then 0 else bv_unsigned a4))] m mx ->
                    wmono rsegs m mx -> nlk_at mx kbs).
      { intros mx MUx WMx. apply (nlk_move _ m mx kbs NK MUx WMx).
        pose proof FG as G1. pose proof KGW as G2. pose proof AGW as G3. unfold hold, apart_gnl in G1, G2, G3.
        clear_tac. }
      lazymatch type of MU with munch ?W _ _ =>
        assert (ITk : forall Wx mx bs', munch Wx m mx -> nk_n_if bs' = nk_n_if kbs -> sub_fp Wx W ->
                        iftab_at mx bs' tab) end.
      { intros Wx mx bs' MUx Hn Sx. eapply iftab_keep; [exact IT | exact MUx | exact Hn | |].
        - intros i Hi. pose proof (proj1 (proj2 IT)) as L80.
          pose proof FG as G1. pose proof EG as G4. pose proof KGW as G2. pose proof AGW as G3.
          unfold hold, apart_gnl in G1, G2, G3, G4.
          split; eapply clear_sub; try exact Sx; clear_tac.
        - intros i n2 ix p Hi Hp. destruct (TN i n2 ix p Hi Hp) as (T1 & T2 & T3 & T4 & T5).
          pose proof (cond_apart _ _ _ _ (proj1 Ra2) T4) as T4'.
          pose proof (cond_apart _ _ _ _ (proj1 Ra4) T5) as T5'.
          clear T4 T5. unfold apart_frame, apart_gnl, apart in T1, T2, T3, T4', T5'. rewrite mkR_sp in T1.
          eapply clear_sub; [|exact Sx]. clear_tac. }
      assert (BZk : forall mx, munch [(bv_unsigned sp - 16672, bv_unsigned sp)] m2 mx -> wmono rsegs m2 mx ->
                      bufz mx (bv_unsigned a1) (bv_unsigned a2) /\ bufz mx (bv_unsigned a3) (bv_unsigned a4)).
      { intros mx MUx WMx. split.
        - apply (bufz_move _ _ _ _ _ KZ MUx WMx). intros H1 H2. destruct (KF H1) as [F1 _].
          unfold apart_frame in F1. rewrite mkR_sp in F1. clear_tac.
        - apply (bufz_move _ _ _ _ _ AZ MUx WMx). intros H1 H2. destruct (AF H1) as [F1 _].
          unfold apart_frame in F1. rewrite mkR_sp in F1. clear_tac. }
      zstep.
      pose proof SN as SN0.
      destruct nm as [s|].
      2:{ (* NULL name: -EINVAL *)
        cbn [str_arg] in SN.
        zstep. if_true.
        do 9 zstep. release_frame FR ST (bv_unsigned sp).
        apply evt_done. do 2 eexists. split; [reflexivity|].
        split; [eapply regs_preserved_mkR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        split; [exact ST|].
        apply (rd_post_refuse (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
                 s11 t3 t4 t5 t6) m _ _ kbs tab None (- E_INVAL) NK IT SN0 WF OP); [reflexivity | reflexivity | | | |].
        - exact (NKk _ MT WM).
        - apply (ITk _ _ kbs MU eq_refl). intros y Hy. exact Hy.
        - exact (proj1 (BZk _ MF WF2)).
        - exact (proj2 (BZk _ MF WF2)). }
      destruct SN as [N0 Ns].
      zstep. if_false.
      destruct (NF s eq_refl) as [NF1 _]. destruct (NA s eq_refl) as [NA1 NA2].
      assert (NB : cstr_at m2 (bv_unsigned a0) s).
      { apply (cstr_move _ m _ _ _ Ns MT).
        pose proof (cond_apart _ _ _ _ (proj1 Ra2) NA1) as D1. pose proof (cond_apart _ _ _ _ (proj1 Ra4) NA2) as D2.
        clear NA1 NA2. unfold apart_frame, apart in NF1, D1, D2. rewrite mkR_sp in NF1. clear_tac. }
      destruct s as [|x s'].
      { (* empty name: -EINVAL *)
        pose proof (bytes_at_read1 m2 a0 (zb 0) [] (proj1 NB)) as HR.
        zstep. unfold zb. zstep. if_true.
        do 9 zstep. release_frame FR ST (bv_unsigned sp).
        apply evt_done. do 2 eexists. split; [reflexivity|].
        split; [eapply regs_preserved_mkR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        split; [exact ST|].
        apply (rd_post_refuse (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
                 s11 t3 t4 t5 t6) m _ _ kbs tab (Some []) (- E_INVAL) NK IT SN0 WF OP);
          [reflexivity | reflexivity | | | |].
        - exact (NKk _ MT WM).
        - apply (ITk _ _ kbs MU eq_refl). intros y Hy. exact Hy.
        - exact (proj1 (BZk _ MF WF2)).
        - exact (proj2 (BZk _ MF WF2)). }
      assert (Hx : bv_unsigned x <> 0) by (intros E; apply (proj2 Ns); left; apply byte_zero; exact E).
      pose proof (bytes_at_read1 m2 a0 x (s' ++ [zb 0]) (proj1 NB)) as HR.
      zstep. zstep.
      assert (Ex : bv_eqb (Z_to_bv 64 (bv_unsigned x)) (Z_to_bv 64 0) = false).
      { rewrite bv_eqb_lit by (pose proof (byte_range x); lia). apply Z.eqb_neq. exact Hx. }
      rewrite Ex. cbv iota. clear HR Ex.
      (* ---- fuzz_if_nametoindex at 0x15f80 ---- *)
      pose proof (NKk _ MT WM) as NK2.
      assert (IT2 : iftab_at m2 kbs tab).
      { apply (ITk _ _ kbs MT eq_refl). intros y Hy. cbn [outside] in *. tauto. }
      pose proof HIX as HIX'. unfold fuzz_if_nametoindex_contract, index_of_contract, FUZZ_IF_NAMETOINDEX in HIX'.
      zstep.
      eapply (leaf_call _ _ _ _ _ HIX').
      { intros r1 r2 mm q1 q2 mm' E1 E2 H. cbv beta in *. unfold arg in *. rewrite <- !E1, <- !E2. exact H. }
      { apply leaf_q_ext. intros q1 q2 mm E H. unfold rd_post in *. cbv beta in *. rewrite <- !E. exact H. }
      { cbv beta. exists kbs, tab, (x :: s'). unfold frame_apart_gnl, apart_frame, apart_gnl.
        rewrite ?mkR_sp, ?mkR_a0. rewrite unsigned_lit by lia.
        split; [exact NK2|]. split; [pose proof FG as G1; unfold apart_gnl in G1; lia|].
        split; [exact IT2|]. split; [exact N0|]. split; [exact NB|].
        split; [unfold apart_frame in NF1; rewrite mkR_sp in NF1; lia|].
        intros i n2 ix p Hi Hp.
        assert (Li : (i < length tab)%nat) by (apply nth_error_Some; congruence).
        pose proof (proj1 (proj2 IT)) as L80.
        apply (u64_back _ m m2 _ _ MT) in Hp.
        2:{ pose proof FG as G1. pose proof KGW as G2. pose proof AGW as G3. unfold hold, apart_gnl in G1, G2, G3.
            clear_tac. }
        destruct (TN i n2 ix p Hi Hp) as (T1 & _). unfold apart_frame in T1. rewrite mkR_sp in T1. lia. }
      { exact MI. }
      { rewrite unsigned_lit by lia. exact ST. }
      { rewrite unsigned_lit by lia. lia. }
      { rewrite unsigned_lit by lia. lia. }
      intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m3 MU3 WM3 MI3 ST3 PO3.
      rewrite ret_pc_even by (lia || reflexivity).
      cbv beta in MU3, PO3. cbv [writes_nothing] in MU3. rewrite ?mkR_sp, unsigned_lit in MU3 by lia.
      rewrite unsigned_lit in ST3 by lia.
      pose proof (PO3 kbs tab (x :: s') NK2 IT2 NB) as IX. clear PO3.
      transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI. rename MI3 into MI, ST3 into ST.
      change (a0' = wz (index_of tab (x :: s'))) in IX. subst a0'.
      assert (IR : 0 <= index_of tab (x :: s') < 2 ^ 31).
      { apply index_of_range. intros i n ix Hi. destruct IT as (_ & _ & E). exact (proj1 (E i n ix Hi)). }
      remember (index_of tab (x :: s')) as idx eqn:Eidx. unfold wz.
      zstep. rewrite bv_eqb_lit by lia.
      destruct (Z.eqb_spec idx 0) as [I0|I0]; cbv iota.
      { (* unknown name: -ENODEV *)
        zstep. do 9 zstep. release_frame FR ST (bv_unsigned sp).
        apply evt_done. do 2 eexists. split; [reflexivity|].
        split; [eapply regs_preserved_mkR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        split; [exact ST|].
        apply (rd_post_refuse (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
                 s11 t3 t4 t5 t6) m _ _ kbs tab (Some (x :: s')) (- E_NODEV) NK IT SN0 WF OP);
          [ | reflexivity | | | |].
        - unfold read_lib, read_core. cbn [length Nat.eqb]. rewrite <- Eidx, I0. reflexivity.
        - exact (NKk _ MT WM).
        - apply (ITk _ _ kbs MU eq_refl). intros y Hy. exact Hy.
        - exact (proj1 (BZk _ MF WF2)).
        - exact (proj2 (BZk _ MF WF2)). }
      (* ---- the request: memset(sp + 12, 0, 20) at 0x15f98, then the four header stores ---- *)
      lazymatch type of FR with rw_cells _ _ _ (CB 32 ?j :: ?rest) =>
        change (CB 32 j :: rest) with ([CB 32 j] ++ rest) in FR end.
      apply rw_cells_app in FR. destruct FR as [FRj FRc].
      cbn [cells_size csize] in FRc.
      replace (bv_unsigned sp + -80 + Z.of_nat (32 + 0)) with (bv_unsigned sp + -48) in FRc by lia.
      change 32%nat with (12 + 20)%nat in FRj.
      destruct (rw_cells_cut _ _ _ _ _ FRj) as (ja & jb & FRa & FRb). clear FRj.
      replace (bv_unsigned sp + -80 + Z.of_nat 12) with (bv_unsigned sp + -68) in FRb by lia.
      do 5 zstep.
      eapply evt_cut.
      { eapply HMS; [|exact MI].
        rewrite !unsigned_lit by lia.
        lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -68) by lia end.
        exact FRb. }
      intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
                  & m4 & -> & MU4 & WM4 & MI4 & RW4).
      rewrite ret_pc_even by (lia || reflexivity).
      rewrite !unsigned_lit in MU4, RW4 by lia.
      lazymatch type of MU4 with munch [(?A, ?B)] _ _ =>
        replace A with (bv_unsigned sp + -68) in MU4 by lia; replace B with (bv_unsigned sp + -48) in MU4 by lia end.
      lazymatch type of RW4 with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -68) in RW4 by lia end.
      transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4 MI. rename MI4 into MI, RW4 into FRb.
      change (Z.to_nat 20) with 20%nat in FRb.
      do 8 zstep.
      (* ---- nl_talk(sp, 32, kind, kind_n, alias, alias_n) at 0x15fd4 ---- *)
      let m5 := curmem in
      assert (RQ : bytes_at rsegs m5 (bv_unsigned sp + -80) (req_read idx)).
      { lazymatch type of FRa with rw_cells _ _ _ [C4 ?v0; C4 ?v1; C4 ?v2] =>
        lazymatch type of FRb with rw_cells _ _ _ [CB 8 ?j1; C4 ?v3; CB 8 ?j2] =>
          rewrite <- (req_cells idx v0 v1 v2 v3 j1 j2 IR eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) end end.
        apply bytes_at_app. split; [exact (rw_cells_bytes _ _ _ FRa)|].
        lazymatch goal with |- bytes_at _ _ ?A _ => replace A with (bv_unsigned sp + -68) end;
          [exact (rw_cells_bytes _ _ _ FRb)|].
        cbn [cells_bytes cbytes]. rewrite !length_app, !length_le4. cbn [length]. lia. }
      lazymatch type of FRa with rw_cells _ _ _ ?csa =>
      lazymatch type of FRb with rw_cells _ _ _ ?csb =>
      lazymatch type of FRc with rw_cells _ _ _ ?csc =>
        let m5 := curmem in
        assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -80) (csa ++ csb ++ csc)) end end end.
      { apply rw_cells_app. split; [exact FRa|]. apply rw_cells_app. split.
        - lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -68) by (cbn; lia) end.
          exact FRb.
        - lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -48) by (cbn; lia) end.
          exact FRc. }
      cbn [app] in FR5. clear FRa FRb FRc.
      destruct (BZk _ MF WF2) as [KZ5 AZ5].
      pose proof (NKk _ MT WM) as NK5.
      pose proof (wr_at_transport rsegs _ _ _ _ (proj1 ER0) WM) as ER5.
      do 7 zstep.
      pose proof HNT as HNT'. unfold nl_talk_contract, NL_TALK in HNT'.
      eapply (leaf_call _ _ _ _ _ HNT').
      { intros r1 r2 mm q1 q2 mm' E1 E2 H. cbv beta in *. unfold arg in *. rewrite <- !E1, <- !E2. exact H. }
      { apply leaf_q_ext. intros q1 q2 mm E H. unfold rd_post in *. cbv beta in *. rewrite <- !E. exact H. }
      { cbv beta. exists kbs, (req_read idx).
        unfold frame_apart_gnl, apart_frame.
        rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_errno.
        rewrite !unsigned_lit by lia.
        pose proof FG as G1. pose proof EF as G2. pose proof EG as G3.
        unfold apart_gnl in G1, G3. unfold apart_frame in G2. rewrite mkR_sp in G2.
        split; [exact NK5|]. split; [unfold apart_gnl; lia|]. split; [exact WF|]. split; [exact OP|].
        split; [exact ER5|]. split; [lia|]. split; [exact EG|].
        split; [exact RQ|]. split; [reflexivity|]. split; [unfold NL_SENT_LEN; lia|].
        split; [intros H1 H2; exact (proj2 (KZ5 H1 H2))|]. split; [intros H1 H2; exact (proj2 (AZ5 H1 H2))|].
        split; [unfold apart; lia|]. split; [exact KE|]. split; [exact AE|]. split; [exact KA|].
        split; [exact OPN|]. split; [exact CLN|].
        split; [unfold apart_gnl; lia|]. split; [lia|].
        split; [intros H; destruct (KF H) as [F1 F2]; unfold apart_frame in F1; rewrite mkR_sp in F1;
                split; [lia | exact F2]|].
        intros H; destruct (AF H) as [F1 F2]; unfold apart_frame in F1; rewrite mkR_sp in F1;
        split; [lia | exact F2]. }
      { exact MI. }
      { rewrite unsigned_lit by lia. exact ST. }
      { rewrite unsigned_lit by lia. lia. }
      { rewrite unsigned_lit by lia. lia. }
      intros ra6 t06 t16 t26 a06 a16 a26 a36 a46 a56 a66 a76 t36 t46 t56 t66 m6 MU6 WM6 MI6 ST6 PO6.
      rewrite ret_pc_even by (lia || reflexivity).
      cbv beta in MU6, PO6.
      rewrite ?mkR_sp, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_errno in MU6. rewrite !unsigned_lit in MU6 by lia.
      rewrite unsigned_lit in ST6 by lia.
      lazymatch type of FR5 with rw_cells _ _ _ ?cs5 =>
        assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -80) cs5) end.
      { apply (rw_cells_transport rsegs _ _ m6 _ _ FR5 MU6 WM6).
        pose proof FG as G1. pose proof EF as G2. pose proof KFW as G4. pose proof AFW as G5.
        unfold apart_gnl in G1. unfold apart_frame in G2. rewrite mkR_sp in G2. unfold hold in G4, G5.
        cbn [disjoint_from cells_size csize]. repeat split; try exact I; lia. }
      lazymatch type of MU with munch ?W _ _ => assert (MU7 : munch W m m6) end.
      { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU6]. intros y Hy. cbn [outside] in *.
        destruct Hy as (H1 & H2 & H3 & H4 & H5 & _). repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM6) as WM7.
      specialize (PO6 kbs (req_read idx) NK5).
      rewrite ?mkR_a0, ?mkR_a1, !unsigned_lit in PO6 by lia.
      specialize (PO6 RQ eq_refl). cbv zeta in PO6.
      destruct PO6 as (RC6 & NL6 & KS6 & AS6 & KN6 & AN6 & KR6 & AR6).
      do 11 zstep. release_frame FR6 ST6 (bv_unsigned sp).
      apply evt_done. do 2 eexists. split; [reflexivity|].
      split; [eapply regs_preserved_mkR|]. split; [exact MU7|]. split; [exact WM7|]. split; [exact MI6|].
      split; [exact ST6|].
      rewrite Eidx in NL6.
      eapply (rd_post_talk (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
                 s11 t3 t4 t5 t6) m _ _ kbs tab (x :: s') NK IT SN0 WF ltac:(discriminate)).
      - rewrite <- Eidx. exact I0.
      - exact RC6.
      - exact NL6.
      - intros bs' Hn. apply (ITk _ _ bs' MU7 Hn). intros y Hy. exact Hy.
      - exact KS6.
      - exact AS6.
      - intros H1 H2 H3. apply (KN6 H1 H2 []); [rewrite mkR_a3; rewrite mkR_a2 in H3; cbn [length Z.of_nat]; lia|].
        exact (proj1 (KZ5 H2 H3)).
      - intros H1 H2 H3. apply (AN6 H1 H2 []); [rewrite mkR_a5; rewrite mkR_a4 in H3; cbn [length Z.of_nat]; lia|].
        exact (proj1 (AZ5 H2 H3)).
      - exact KR6.
      - exact AR6. }
    { (* ---------------- MID: the alias NUL store, 0x15f64 .. 0x15f6c ---------------- *)
      intros m2 FR2 ST2 MU2 MT2 MK2 WM2 MI2 KZ.
      clear FR ST MU MT MK M0 WM MI.
      rename FR2 into FR, ST2 into ST, MU2 into MU, MT2 into MT, MK2 into MK, WM2 into WM, MI2 into MI.
      destruct (Z.eq_dec (bv_unsigned a3) 0) as [A0|A0].
      { zstep. if_true. apply REST; try assumption. intros H; contradiction. }
      destruct (Z.eq_dec (bv_unsigned a4) 0) as [AN|AN].
      { zstep. if_false. zstep. if_true. apply REST; try assumption. intros _ H; lia. }
      zstep. if_false. zstep. if_false.
      assert (AW : (if bv_unsigned a3 =? 0 then 0 else bv_unsigned a4) = bv_unsigned a4)
        by (destruct (Z.eqb_spec (bv_unsigned a3) 0); [contradiction | reflexivity]).
      destruct (BA A0 ltac:(lia)) as [ja AB].
      destruct (AF A0) as [AF1 _]. unfold apart_frame in AF1. rewrite mkR_sp in AF1.
      assert (DAK : (if bv_unsigned a1 =? 0 then 0 else bv_unsigned a2) = 0 \/
                    apart (bv_unsigned a3) (bv_unsigned a4) (bv_unsigned a1)
                          (if bv_unsigned a1 =? 0 then 0 else bv_unsigned a2)).
      { apply cond_apart; [lia|]. intros H1 H2. apply apart_sym. exact (KA H1 H2 A0 ltac:(lia)). }
      unfold apart in DAK.
      let mp := curmem in
      assert (ABp : rw_cells rsegs mp (bv_unsigned a3) [CB (Z.to_nat (bv_unsigned a4)) ja])
        by (apply (rw_cells_move _ m mp _ _ AB MK WM); cbn [cells_size csize];
            rewrite Nat.add_0_r, Z2Nat.id by lia; clear_tac).
      clear AB MK DAK.
      replace (Z.to_nat (bv_unsigned a4)) with (1 + (Z.to_nat (bv_unsigned a4) - 1))%nat in ABp by lia.
      destruct (rw_cells_cut _ _ _ _ _ ABp) as (j1 & j2 & AB1 & ABr). clear ABp.
      replace (bv_unsigned a3 + Z.of_nat 1) with (bv_unsigned a3 + 1) in ABr by lia.
      let mp := curmem in
      pose proof (munch_refl [(bv_unsigned a3, bv_unsigned a3 + 1)] mp) as MA;
      pose proof (wmono_refl rsegs mp) as WMA;
      assert (KZ' : bufz mp (bv_unsigned a1) (bv_unsigned a2) /\ True) by (split; [exact KZ | exact I]).
      clear KZ.
      nul_store AB1 a3.
      let m3 := curmem in
      assert (AZ : bufz m3 (bv_unsigned a3) (bv_unsigned a4)).
      { intros _ _. split.
        - split; [|intros []]. exact (rw_cells_bytes _ _ _ AB1).
        - exists (Z_to_bv 8 0 :: j2).
          replace (Z.to_nat (bv_unsigned a4)) with (S (Z.to_nat (bv_unsigned a4) - 1)) by lia.
          apply rw_cells_c1_cb; [exact AB1 | exact ABr]. }
      let m3 := curmem in
      assert (KZ : bufz m3 (bv_unsigned a1) (bv_unsigned a2)).
      { apply (bufz_move _ _ _ _ _ (proj1 KZ') MA WMA). intros H1 H2.
        pose proof (KA H1 H2 A0 ltac:(lia)) as D. unfold apart in D. clear_tac. }
      apply REST; assumption. }
    (* ---------------- the kind NUL store, 0x15f58 .. 0x15f60 ---------------- *)
    clear REST.
    destruct (Z.eq_dec (bv_unsigned a1) 0) as [K0|K0].
    { zstep. if_true. clear M0. apply MID; try assumption. intros H; contradiction. }
    destruct (Z.eq_dec (bv_unsigned a2) 0) as [N0|N0].
    { zstep. if_false. zstep. if_true. clear M0. apply MID; try assumption. intros _ H; lia. }
    zstep. if_false. zstep. if_false.
    assert (KW : (if bv_unsigned a1 =? 0 then 0 else bv_unsigned a2) = bv_unsigned a2)
      by (destruct (Z.eqb_spec (bv_unsigned a1) 0); [contradiction | reflexivity]).
    destruct (BK K0 ltac:(lia)) as [jk KB].
    destruct (KF K0) as [KF1 _]. unfold apart_frame in KF1. rewrite mkR_sp in KF1.
    let mp := curmem in
    assert (KBp : rw_cells rsegs mp (bv_unsigned a1) [CB (Z.to_nat (bv_unsigned a2)) jk])
      by (apply (rw_cells_move _ m mp _ _ KB M0 WM); cbn [cells_size csize];
          rewrite Nat.add_0_r, Z2Nat.id by lia; clear_tac).
    clear KB M0.
    replace (Z.to_nat (bv_unsigned a2)) with (1 + (Z.to_nat (bv_unsigned a2) - 1))%nat in KBp by lia.
    destruct (rw_cells_cut _ _ _ _ _ KBp) as (j1 & j2 & KB1 & KBr). clear KBp.
    replace (bv_unsigned a1 + Z.of_nat 1) with (bv_unsigned a1 + 1) in KBr by lia.
    nul_store KB1 a1.
    let m3 := curmem in
    assert (KZ : bufz m3 (bv_unsigned a1) (bv_unsigned a2)).
    { intros _ _. split.
      - split; [|intros []]. exact (rw_cells_bytes _ _ _ KB1).
      - exists (Z_to_bv 8 0 :: j2).
        replace (Z.to_nat (bv_unsigned a2)) with (S (Z.to_nat (bv_unsigned a2) - 1)) by lia.
        apply rw_cells_c1_cb; [exact KB1 | exact KBr]. }
    apply MID; assumption.
Qed.

Print Assumptions reac_link_alias_read_holds.
