(* op_read (fuzz_link.c:677-700), plain image: the Pre of each leaf callee of the arm, from the facts its
   cuts carry (a Theorem Labs lane), and the register-extensionality (`post_ext`) of each callee's Post, which
   LC0Call.v's `leaf_call` asks for.

   This file takes no hypothesis: it only proves `Pre regs m` of the contracts as they stand in
   lib/Prog/<f>_c.v. The Pre, Wr and Post of each contract are read out of the contract's own text
   (`c0_<f>_Pre` / `c0_<f>_Post`, by Ltac, so they are the contract's terms and not a restatement), and
   `c0_<f>_is` checks the contract is `leaf` of them. Each `c0_<f>_pre` is stated over an abstract
   register map with `spZ regs = e_S E - SLOT_FRAME` and `arg regs k = ...`, so a walk applies it to
   its `mkR ...` map through lib/Prog/mk_leaf.v's `mkR_sp`, `mkR_a0` .. `mkR_a7`, `mkR_errno`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import kernel_c model_read_c
  reac_link_alias_read_c index_of_c check_socket_c check_refused_c check_bounds_c check_read_c
  check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC0Defs LC0Lib.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The parts of each contract
   ========================================================================== *)

Ltac c0_part c k :=
  let t := eval cbv beta delta [c index_of_contract] in c in
  lazymatch t with leaf _ _ ?P ?W ?Q =>
    lazymatch k with 1 => exact P | 2 => exact W | 3 => exact Q end end.

Definition c0_kernel_Pre := ltac:(c0_part kernel_contract 1).
Definition c0_kernel_Wr := ltac:(c0_part kernel_contract 2).
Definition c0_kernel_Post := ltac:(c0_part kernel_contract 3).
Lemma c0_kernel_is : kernel_contract = leaf KERNEL 4416 c0_kernel_Pre c0_kernel_Wr c0_kernel_Post.
Proof. reflexivity. Qed.

Definition c0_model_read_Pre := ltac:(c0_part model_read_contract 1).
Definition c0_model_read_Wr := ltac:(c0_part model_read_contract 2).
Definition c0_model_read_Post := ltac:(c0_part model_read_contract 3).
Lemma c0_model_read_is :
  model_read_contract = leaf MODEL_READ 240 c0_model_read_Pre c0_model_read_Wr c0_model_read_Post.
Proof. reflexivity. Qed.

Definition c0_alias_read_Pre := ltac:(c0_part reac_link_alias_read_contract 1).
Definition c0_alias_read_Wr := ltac:(c0_part reac_link_alias_read_contract 2).
Definition c0_alias_read_Post := ltac:(c0_part reac_link_alias_read_contract 3).
Lemma c0_alias_read_is : reac_link_alias_read_contract =
  leaf REAC_LINK_ALIAS_READ 16672 c0_alias_read_Pre c0_alias_read_Wr c0_alias_read_Post.
Proof. reflexivity. Qed.

Definition c0_index_of_Pre := ltac:(c0_part index_of_contract_P 1).
Definition c0_index_of_Wr := ltac:(c0_part index_of_contract_P 2).
Definition c0_index_of_Post := ltac:(c0_part index_of_contract_P 3).
Lemma c0_index_of_is : index_of_contract_P = leaf INDEX_OF 48 c0_index_of_Pre c0_index_of_Wr c0_index_of_Post.
Proof. reflexivity. Qed.

Definition c0_check_socket_Pre := ltac:(c0_part check_socket_contract 1).
Definition c0_check_socket_Post := ltac:(c0_part check_socket_contract 3).
Lemma c0_check_socket_is :
  check_socket_contract = leaf CHECK_SOCKET 0 c0_check_socket_Pre writes_nothing c0_check_socket_Post.
Proof. reflexivity. Qed.

Definition c0_check_refused_Pre := ltac:(c0_part check_refused_contract 1).
Definition c0_check_refused_Post := ltac:(c0_part check_refused_contract 3).
Lemma c0_check_refused_is :
  check_refused_contract = leaf CHECK_REFUSED 0 c0_check_refused_Pre writes_nothing c0_check_refused_Post.
Proof. reflexivity. Qed.

Definition c0_check_bounds_Pre := ltac:(c0_part check_bounds_contract 1).
Definition c0_check_bounds_Post := ltac:(c0_part check_bounds_contract 3).
Lemma c0_check_bounds_is :
  check_bounds_contract = leaf CHECK_BOUNDS 32 c0_check_bounds_Pre writes_nothing c0_check_bounds_Post.
Proof. reflexivity. Qed.

Definition c0_check_read_Pre := ltac:(c0_part check_read_contract 1).
Definition c0_check_read_Post := ltac:(c0_part check_read_contract 3).
Lemma c0_check_read_is :
  check_read_contract = leaf CHECK_READ 32 c0_check_read_Pre writes_nothing c0_check_read_Post.
Proof. reflexivity. Qed.

Definition c0_check_requests_Pre := ltac:(c0_part check_requests_contract 1).
Definition c0_check_requests_Post := ltac:(c0_part check_requests_contract 3).
Lemma c0_check_requests_is :
  check_requests_contract = leaf CHECK_REQUESTS 48 c0_check_requests_Pre writes_nothing c0_check_requests_Post.
Proof. reflexivity. Qed.

(* ==========================================================================
   2. post_ext of each Post: a Post reads registers only through getr
   ========================================================================== *)

Ltac c0_pext P :=
  unfold post_ext, P; intros r1 r2 m q1 q2 m' Hr Hq H; unfold getr_same in Hr, Hq;
  cbv beta in *; unfold arg, res, errno_at in *; rewrite <- ?Hr, <- ?Hq; exact H.

Lemma c0_kernel_post_ext : post_ext c0_kernel_Post.
Proof. c0_pext c0_kernel_Post. Qed.
Lemma c0_model_read_post_ext : post_ext c0_model_read_Post.
Proof. c0_pext c0_model_read_Post. Qed.
Lemma c0_alias_read_post_ext : post_ext c0_alias_read_Post.
Proof. c0_pext c0_alias_read_Post. Qed.
Lemma c0_index_of_post_ext : post_ext c0_index_of_Post.
Proof. c0_pext c0_index_of_Post. Qed.
Lemma c0_check_socket_post_ext : post_ext c0_check_socket_Post.
Proof. c0_pext c0_check_socket_Post. Qed.
Lemma c0_check_refused_post_ext : post_ext c0_check_refused_Post.
Proof. c0_pext c0_check_refused_Post. Qed.
Lemma c0_check_bounds_post_ext : post_ext c0_check_bounds_Post.
Proof. c0_pext c0_check_bounds_Post. Qed.
Lemma c0_check_read_post_ext : post_ext c0_check_read_Post.
Proof. c0_pext c0_check_read_Post. Qed.
Lemma c0_check_requests_post_ext : post_ext c0_check_requests_Post.
Proof. c0_pext c0_check_requests_Post. Qed.

(* ==========================================================================
   3. The Pre of each callee from the cut facts
   ========================================================================== *)

(* kernel (in) at 0x13e24: a0 = sp + 0x40, the cursor cells, the payload suffix at the cursor *)
Lemma c0_kernel_pre : forall E regs m P N kbs,
  lenv_ok E -> spZ regs = e_S E - SLOT_FRAME -> arg regs 0 = e_S E - SLOT_FRAME + FO_P ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] ->
  cursor_ok m (e_p0 E) (e_pl E) P N ->
  nlk_at m kbs -> nlk_wf kbs -> iftab_at m kbs link_tab -> ifptrs_at m -> texts_at m -> la_ok m ->
  mem_inv rsegs m ->
  c0_kernel_Pre regs m.
Proof.
  intros E regs m P N kbs HE SP A0 CC CU NL NW IT IP TX LA MI.
  pose proof HE as HE'. destruct HE' as (HS1 & HS2 & _ & _ & _ & _ & _ & _ & HPL & (P1 & P2 & P3) & _).
  destruct CU as (PB & k & Hk & EP & EN).
  pose proof (c0_img_free _ _ P3 ltac:(lia)) as PF.
  assert (FX : forall p n, c0_fixed_w p n -> kernel_apart regs p n).
  { intros p n F. destruct (c0_fixed_ctx E regs 4416 p n HE SP ltac:(lia) F) as (F1 & F2 & _ & _ & F5 & _ & F7).
    unfold kernel_apart. rewrite A0. split; [exact F1|]. split; [exact F2|]. split; [exact F5|].
    destruct (F7 FO_P 16 ltac:(c0_unf; lia) ltac:(lia) ltac:(c0_unf; lia)) as [_ A]. unfold apart in A. lia. }
  assert (UP : bv_unsigned (wz P) = P) by (apply c0_wz_u; c0_unf; lia).
  assert (UN : bv_unsigned (wz N) = N) by (apply c0_wz_u; c0_unf; lia).
  unfold c0_kernel_Pre. exists kbs, (wz P), (wz N). cbv beta. rewrite UP, UN, A0.
  repeat match goal with |- _ /\ _ => split end.
  - exact NL.
  - unfold frame_apart_gnl, apart_gnl. rewrite SP. c0_unf; lia.
  - exact NW.
  - exact CC.
  - unfold apart_gnl. c0_unf; lia.
  - unfold apart_frame. rewrite SP. c0_unf; lia.
  - exists (skipn (Z.to_nat k) (e_pl E)). split.
    + rewrite EP. replace (e_p0 E + k) with (e_p0 E + Z.of_nat (Z.to_nat k)) by lia.
      apply c0_bytes_skip; [exact PB | lia].
    + rewrite length_skipn. lia.
  - unfold kernel_apart, apart_frame, apart_gnl. rewrite SP, A0. c0_unf; lia.
  - unfold kernel_apart, apart_frame, apart_gnl. rewrite SP, A0. c0_unf; lia.
  - intros i Hi. unfold TEXTS_N in Hi.
    destruct (c0_texts_img m MI (Z.to_nat i) ltac:(lia)) as (s & sl & B & NZ & SL & LS & F).
    exists (nth (Z.to_nat i) texts_ptrs 0), s, sl.
    split; [|split; [|split; [exact B|split; [exact NZ|split; [exact SL|split; [exact LS|]]]]]].
    + pose proof (TX (Z.to_nat i) ltac:(lia)) as U. rewrite Z2Nat.id in U by lia. exact U.
    + (* every texts entry is a .rodata address, so not 0 (kernel_c.v's texts clause asks it) *)
      assert (HT : forall t, (t < 11)%nat -> nth t texts_ptrs 0 <> 0).
      { intros t Ht. do 11 (destruct t as [|t]; [unfold texts_ptrs; cbn [nth]; lia|]). lia. }
      apply HT. lia.
    + apply FX. apply c0_fixed_w_of. exact F.
  - exact LA.
  - unfold apart_frame. rewrite SP. c0_unf; lia.
  - c0_unf; lia.
  - intros tab i nm ix p IT' Hi Hp. destruct (c0_ifname m kbs tab i nm ix p IT IP IT' Hi Hp) as [F _].
    exact (FX _ _ F).
Qed.

(* model_read (m, name, kc ? wk : NULL, kc, ac ? wa : NULL, ac) at 0x13eb4 *)
Lemma c0_model_read_pre : forall E regs m P N wa wk sel kc ac kbs mbs,
  lenv_ok E -> spZ regs = e_S E - SLOT_FRAME ->
  arg regs 0 = e_md E -> arg regs 1 = sel_ptr sel ->
  (arg regs 2 = 0 \/ arg regs 2 = e_S E - SLOT_FRAME + FO_B256) -> arg regs 3 = kc ->
  (arg regs 4 = 0 \/ arg regs 4 = e_S E - SLOT_FRAME + FO_B40) -> arg regs 5 = ac ->
  0 <= sel < 256 -> 0 <= kc <= 40 -> 0 <= ac <= 40 ->
  c0_frame E P N wa wk m -> model_at m (e_md E) mbs -> model_wf mbs ->
  nlk_at m kbs -> nlk_wf kbs -> iftab_at m kbs link_tab -> ifptrs_at m -> gnames_at m -> odd_at m ->
  c0_model_read_Pre regs m.
Proof.
  intros E regs m P N wa wk sel kc ac kbs mbs HE SP A0 A1 A2 A3 A4 A5 Hs Hk Ha FR MD MW NL NW IT IP GN OD.
  pose proof HE as HE'. destruct HE' as (HS1 & HS2 & _ & (D1 & D2 & D3) & _).
  pose proof (c0_img_free _ _ D3 ltac:(c0_unf; lia)) as DF.
  destruct (c0_frame_bufs E P N wa wk m FR) as [BA BK].
  assert (NM : forall s, sel_name sel = Some s -> c0_fixed_w (arg regs 1) (Z.of_nat (length s) + 1)).
  { intros s Hs'. rewrite A1. apply c0_fixed_w_of. exact (proj2 (c0_sel_fixed sel s Hs Hs')). }
  assert (IF : forall i n2 ix p, nth_error link_tab i = Some (n2, ix) ->
     u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> c0_fixed_w p (Z.of_nat (length n2) + 1)).
  { intros i n2 ix p Hi Hp. exact (proj1 (c0_ifname m kbs link_tab i n2 ix p IT IP IT Hi Hp)). }
  assert (B2 : arg regs 2 <> 0 -> arg regs 2 = e_S E - SLOT_FRAME + FO_B256)
    by (intros H; destruct A2 as [A2|A2]; [contradiction | exact A2]).
  assert (B4 : arg regs 4 <> 0 -> arg regs 4 = e_S E - SLOT_FRAME + FO_B40)
    by (intros H; destruct A4 as [A4|A4]; [contradiction | exact A4]).
  unfold c0_model_read_Pre. exists mbs, kbs, link_tab, (sel_name sel). cbv beta. rewrite A0, A3, A5.
  repeat match goal with |- _ /\ _ => split end.
  - exact MD.
  - exact MW.
  - exact NL.
  - unfold frame_apart_gnl, apart_gnl. rewrite SP. c0_unf; lia.
  - exact NW.
  - exact IT.
  - rewrite A1. exact (c0_sel_str m sel Hs GN OD).
  - intros H2 Hc. rewrite (B2 H2). exists (firstn (Z.to_nat kc) wk).
    apply (c0_cb_prefix m _ 40 wk); [exact BK | lia].
  - intros H4 Hc. rewrite (B4 H4). exists (firstn (Z.to_nat ac) wa).
    apply (c0_cb_prefix m _ 40 wa); [exact BA | lia].
  - unfold apart_gnl. destruct DF; c0_unf; lia.
  - unfold apart_frame. rewrite SP. c0_unf; lia.
  - intros _ s Hs'. exact (proj1 (c0_fixed_ctx E regs 240 _ _ HE SP ltac:(lia) (NM s Hs'))).
  - intros H2. rewrite (B2 H2). unfold apart_frame. rewrite SP. c0_unf; lia.
  - intros H4. rewrite (B4 H4). unfold apart_frame. rewrite SP. c0_unf; lia.
  - intros i n2 ix p Hi Hp. exact (proj1 (c0_fixed_ctx E regs 240 _ _ HE SP ltac:(lia) (IF i n2 ix p Hi Hp))).
  - intros s Hs'. destruct (c0_fixed_ctx E regs 240 _ _ HE SP ltac:(lia) (NM s Hs')) as (_ & _ & _ & _ & _ & _ & F7).
    split.
    + intros H2 Hc. rewrite (B2 H2). exact (proj1 (F7 FO_B256 kc ltac:(c0_unf; lia) ltac:(lia) ltac:(c0_unf; lia))).
    + intros H4 Hc. rewrite (B4 H4). exact (proj1 (F7 FO_B40 ac ltac:(c0_unf; lia) ltac:(lia) ltac:(c0_unf; lia))).
  - intros H2 Hc. rewrite (B2 H2). split; [unfold apart_gnl; c0_unf; lia|]. split; [unfold apart; c0_unf; lia|].
    intros i n2 ix p Hi Hp.
    destruct (c0_fixed_ctx E regs 240 _ _ HE SP ltac:(lia) (IF i n2 ix p Hi Hp)) as (_ & _ & _ & _ & _ & _ & F7).
    exact (proj1 (F7 FO_B256 kc ltac:(c0_unf; lia) ltac:(lia) ltac:(c0_unf; lia))).
  - intros H4 Hc. rewrite (B4 H4). split; [unfold apart_gnl; c0_unf; lia|]. split; [unfold apart; c0_unf; lia|].
    intros i n2 ix p Hi Hp.
    destruct (c0_fixed_ctx E regs 240 _ _ HE SP ltac:(lia) (IF i n2 ix p Hi Hp)) as (_ & _ & _ & _ & _ & _ & F7).
    exact (proj1 (F7 FO_B40 ac ltac:(c0_unf; lia) ltac:(lia) ltac:(c0_unf; lia))).
  - intros H2 H4 Hc Ha'. rewrite (B2 H2), (B4 H4). unfold apart. c0_unf; lia.
Qed.

(* reac_link_alias_read (name, kind, kc, alias, ac) at 0x13ed0 *)
Lemma c0_alias_read_pre : forall E regs m sel kc ac K A i kbs,
  lenv_ok E -> spZ regs = e_S E - SLOT_FRAME -> errno_at regs = A_ERRNO ->
  arg regs 0 = sel_ptr sel -> arg regs 1 = K -> arg regs 2 = kc -> arg regs 3 = A -> arg regs 4 = ac ->
  0 <= sel < 256 -> 0 <= kc -> 0 <= ac ->
  c0_buf E kc K m -> c0_buf E ac A m -> (kc <> 0 -> ac <> 0 -> apart K (kc + 1) A (ac + 1)) ->
  nlk_at m kbs -> nlk_wf kbs -> nk_open kbs = 0 ->
  0 <= i <= 47 -> nk_opened kbs <= 64 * i + 1 -> nk_opened kbs = nk_closed kbs ->
  iftab_at m kbs link_tab -> ifptrs_at m -> gnames_at m -> odd_at m -> wr_at rsegs m A_ERRNO 4 ->
  c0_alias_read_Pre regs m.
Proof.
  intros E regs m sel kc ac K A i kbs HE SP ER A0 A1 A2 A3 A4 Hs Hk Ha CK CA AP NL NW NO Hi Ho Hc IT IP GN OD EW.
  pose proof HE as HE'. destruct HE' as (HS1 & HS2 & _).
  assert (BK : K <> 0 -> kc <> 0 /\ blk_out (e_S E) K (kc + 1) /\ exists bs, tbuf_at m K kc bs).
  { intros HK. destruct CK as [Z0 NZ]. destruct (Z.eq_dec kc 0) as [E0|E0]; [exfalso; exact (HK (Z0 E0))|].
    destruct (NZ E0) as (_ & (B & _) & T). split; [exact E0|]. split; [exact B | eexists; exact T]. }
  assert (BA : A <> 0 -> ac <> 0 /\ blk_out (e_S E) A (ac + 1) /\ exists bs, tbuf_at m A ac bs).
  { intros HA. destruct CA as [Z0 NZ]. destruct (Z.eq_dec ac 0) as [E0|E0]; [exfalso; exact (HA (Z0 E0))|].
    destruct (NZ E0) as (_ & (B & _) & T). split; [exact E0|]. split; [exact B | eexists; exact T]. }
  assert (NM : forall s, sel_name sel = Some s -> c0_fixed_w (arg regs 0) (Z.of_nat (length s) + 1)).
  { intros s Hs'. rewrite A0. apply c0_fixed_w_of. exact (proj2 (c0_sel_fixed sel s Hs Hs')). }
  assert (IF : forall i n2 ix p, nth_error link_tab i = Some (n2, ix) ->
     u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> c0_fixed_w p (Z.of_nat (length n2) + 1)).
  { intros i' n2 ix p Hi' Hp. exact (proj1 (c0_ifname m kbs link_tab i' n2 ix p IT IP IT Hi' Hp)). }
  (* a name against the two heap blocks *)
  assert (NB : forall p n, c0_fixed_w p n ->
     (K <> 0 -> 1 <= kc -> apart p n K kc /\ apart K kc p n) /\ (A <> 0 -> 1 <= ac -> apart p n A ac /\ apart A ac p n)).
  { intros p n F. destruct (c0_fixed_ctx E regs 16672 p n HE SP ltac:(lia) F) as (_ & _ & _ & _ & _ & F6 & _).
    split.
    - intros HK _. destruct (BK HK) as (_ & B & _). destruct (F6 K (kc + 1) B ltac:(lia)) as [X1 X2].
      split; (eapply c0_apart_le; [eassumption | lia | lia]).
    - intros HA _. destruct (BA HA) as (_ & B & _). destruct (F6 A (ac + 1) B ltac:(lia)) as [X1 X2].
      split; (eapply c0_apart_le; [eassumption | lia | lia]). }
  unfold c0_alias_read_Pre. exists kbs, link_tab, (sel_name sel). cbv beta. rewrite ER, A1, A2, A3, A4.
  repeat match goal with |- _ /\ _ => split end.
  - exact NL.
  - unfold frame_apart_gnl, apart_gnl. rewrite SP. c0_unf; lia.
  - exact NW.
  - exact NO.
  - lia.
  - lia.
  - exact IT.
  - exact EW.
  - unfold apart_frame. rewrite SP. c0_unf; lia.
  - unfold apart_gnl. c0_unf; lia.
  - rewrite A0. exact (c0_sel_str m sel Hs GN OD).
  - intros HK Hc1. destruct (BK HK) as (_ & _ & bs & T). exists bs.
    unfold tbuf_at in T. change [CB (Z.to_nat kc) bs; C1 (zb GUARD_BYTE)] with ([CB (Z.to_nat kc) bs] ++ [C1 (zb GUARD_BYTE)]) in T.
    exact (proj1 (c0_rw_app _ _ _ _ T)).
  - intros HA Hc1. destruct (BA HA) as (_ & _ & bs & T). exists bs.
    unfold tbuf_at in T. change [CB (Z.to_nat ac) bs; C1 (zb GUARD_BYTE)] with ([CB (Z.to_nat ac) bs] ++ [C1 (zb GUARD_BYTE)]) in T.
    exact (proj1 (c0_rw_app _ _ _ _ T)).
  - intros i' n2 ix p Hi' Hp. pose proof (IF i' n2 ix p Hi' Hp) as F.
    destruct (c0_fixed_ctx E regs 16672 p _ HE SP ltac:(lia) F) as (F1 & F2 & F3 & _).
    destruct (NB p _ F) as [N1 N2].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
    split; [intros H1 H2; exact (proj1 (N1 H1 H2)) | intros H1 H2; exact (proj1 (N2 H1 H2))].
  - intros s Hs'. destruct (NB _ _ (NM s Hs')) as [N1 N2].
    split; [intros H1 H2; exact (proj1 (N1 H1 H2)) | intros H1 H2; exact (proj1 (N2 H1 H2))].
  - intros HK H1 HA H2. apply (c0_apart_le _ _ _ _ _ _ (AP ltac:(lia) ltac:(lia))); lia.
  - intros HK. destruct (BK HK) as (Hk0 & (B1 & B2 & B3) & _).
    destruct (c0_img_named _ _ B3 ltac:(lia)) as (_ & _ & _ & _ & _ & X & _).
    eapply c0_apart_le; [exact (c0_apart_sym _ _ _ _ X) | lia | lia].
  - intros HA. destruct (BA HA) as (Ha0 & (B1 & B2 & B3) & _).
    destruct (c0_img_named _ _ B3 ltac:(lia)) as (_ & _ & _ & _ & _ & X & _).
    eapply c0_apart_le; [exact (c0_apart_sym _ _ _ _ X) | lia | lia].
  - intros s Hs'. destruct (c0_fixed_ctx E regs 16672 _ _ HE SP ltac:(lia) (NM s Hs')) as (F1 & F2 & _).
    split; [exact F1 | exact F2].
  - intros HK. destruct (BK HK) as (Hk0 & (B1 & B2 & B3) & _). pose proof (c0_img_free _ _ B3 ltac:(lia)) as PF.
    unfold apart_frame, apart_gnl. rewrite SP. c0_unf; lia.
  - intros HA. destruct (BA HA) as (Ha0 & (B1 & B2 & B3) & _). pose proof (c0_img_free _ _ B3 ltac:(lia)) as PF.
    unfold apart_frame, apart_gnl. rewrite SP. c0_unf; lia.
Qed.

(* index_of (name) at 0x13eec: a0 = the non-empty name *)
Lemma c0_index_of_pre : forall E regs m sel t kbs,
  lenv_ok E -> spZ regs = e_S E - SLOT_FRAME -> arg regs 0 = sel_ptr sel ->
  0 <= sel < 256 -> sel_name sel = Some t ->
  nlk_at m kbs -> iftab_at m kbs link_tab -> ifptrs_at m -> gnames_at m -> odd_at m ->
  c0_index_of_Pre regs m.
Proof.
  intros E regs m sel t kbs HE SP A0 Hs Ht NL IT IP GN OD.
  pose proof (c0_sel_str m sel Hs GN OD) as SA. rewrite Ht in SA. destruct SA as [NZ C].
  destruct (c0_sel_fixed sel t Hs Ht) as [_ F].
  unfold c0_index_of_Pre. exists kbs, link_tab, t. cbv beta. rewrite A0.
  repeat match goal with |- _ /\ _ => split end.
  - exact NL.
  - unfold frame_apart_gnl, apart_gnl. rewrite SP. destruct HE as (HS1 & HS2 & _). c0_unf; lia.
  - exact IT.
  - exact NZ.
  - exact C.
  - exact (proj1 (c0_fixed_ctx E regs 48 _ _ HE SP ltac:(lia) (c0_fixed_w_of _ _ F))).
  - intros i n2 ix p Hi Hp. destruct (c0_ifname m kbs link_tab i n2 ix p IT IP IT Hi Hp) as [F' _].
    exact (proj1 (c0_fixed_ctx E regs 48 _ _ HE SP ltac:(lia) F')).
Qed.

(* check_socket (&g_nl) at 0x13ed8 *)
Lemma c0_check_socket_pre : forall regs m kbs, nlk_at m kbs -> nk_open kbs = 0 ->
  nk_opened kbs = nk_closed kbs -> nk_misuse kbs = 0 -> c0_check_socket_Pre regs m.
Proof.
  intros regs m kbs NL NO NC NM. unfold c0_check_socket_Pre. exists kbs.
  split; [exact NL|]. split; [exact NO|]. split; [exact NC | exact NM].
Qed.

(* check_bounds (buf, cap) at 0x13f0c / 0x13f20: a heap block of the arm *)
Lemma c0_check_bounds_pre : forall E regs m a cap bs,
  lenv_ok E -> spZ regs = e_S E - SLOT_FRAME -> arg regs 0 = a -> arg regs 1 = cap ->
  a <> 0 -> 1 <= cap -> tbuf_at m a cap bs -> In (zb 0) bs -> c0_blk E a (cap + 1) ->
  c0_check_bounds_Pre regs m.
Proof.
  intros E regs m a cap bs HE SP A0 A1 NZ Hc T In0 ((B1 & B2 & _) & _).
  destruct HE as (HS1 & HS2 & _).
  unfold c0_check_bounds_Pre. exists bs. cbv beta. rewrite A0, A1.
  split; [exact NZ|]. split; [exact Hc|]. split; [exact T|]. split; [exact In0|].
  unfold apart_frame. rewrite SP. c0_unf; lia.
Qed.

(* check_read (rc, want, kind ? kind : wk, wk, alias ? alias : wa, wa) at 0x13f54 *)
Lemma c0_check_read_pre : forall E regs m rc K A k al,
  lenv_ok E -> spZ regs = e_S E - SLOT_FRAME ->
  getr regs 10 = wz rc -> getr regs 11 = wz (norm_rc rc) -> rc < 2 ^ 64 ->
  arg regs 2 = (if K =? 0 then e_S E - SLOT_FRAME + FO_B256 else K) ->
  arg regs 3 = e_S E - SLOT_FRAME + FO_B256 ->
  arg regs 4 = (if A =? 0 then e_S E - SLOT_FRAME + FO_B40 else A) ->
  arg regs 5 = e_S E - SLOT_FRAME + FO_B40 ->
  cstr_at m (e_S E - SLOT_FRAME + FO_B256) k -> cstr_at m (e_S E - SLOT_FRAME + FO_B40) al ->
  (K <> 0 -> cstr_at m K k /\ K + Z.of_nat (length k) + 1 <= e_S E - SLOT_STACK_Z) ->
  (A <> 0 -> cstr_at m A al /\ A + Z.of_nat (length al) + 1 <= e_S E - SLOT_STACK_Z) ->
  c0_check_read_Pre regs m.
Proof.
  intros E regs m rc K A k al HE SP G10 G11 Hrc A2 A3 A4 A5 CK CA HK HA.
  destruct HE as (HS1 & HS2 & _).
  assert (W0 : forall x, wz x = wz 0 -> exists j, x = j * 2 ^ 64).
  { intros x Ex. destruct (c0_wz_pin x 0 Ex ltac:(lia)) as [j Ej]. exists j. lia. }
  unfold c0_check_read_Pre. exists k, k, al, al. cbv beta. rewrite A3, A5, G10, G11.
  repeat match goal with |- _ /\ _ => split end.
  - rewrite A2. destruct (Z.eqb_spec K 0) as [K0|K0]; [exact CK | exact (proj1 (HK K0))].
  - exact CK.
  - rewrite A4. destruct (Z.eqb_spec A 0) as [A0|A0]; [exact CA | exact (proj1 (HA A0))].
  - exact CA.
  - rewrite A2. unfold apart_frame. rewrite SP. destruct (Z.eqb_spec K 0) as [K0|K0].
    + c0_unf; lia.
    + pose proof (proj2 (HK K0)). c0_unf; lia.
  - unfold apart_frame. rewrite SP. c0_unf; lia.
  - rewrite A4. unfold apart_frame. rewrite SP. destruct (Z.eqb_spec A 0) as [A0|A0].
    + c0_unf; lia.
    + pose proof (proj2 (HA A0)). c0_unf; lia.
  - unfold apart_frame. rewrite SP. c0_unf; lia.
  - unfold norm_rc. destruct (Z.ltb_spec 0 rc) as [Hp|Hn].
    + intros _ E0. destruct (W0 rc E0) as [j Ej]. assert (j = 0 \/ j >= 1 \/ j <= -1) as [J|[J|J]] by lia; lia.
    + intros E1 E0. rewrite E0 in E1. symmetry in E1. destruct (W0 RC_FAILS E1) as [j Ej].
      unfold RC_FAILS in Ej. assert (j = 0 \/ j >= 1 \/ j <= -1) as [J|[J|J]] by lia; lia.
  - unfold norm_rc. destruct (Z.ltb_spec 0 rc) as [Hp|Hn]; [intros H; contradiction | intros _; reflexivity].
  - intros _. split; reflexivity.
Qed.

(* check_requests (&g_nl, m) at 0x13f5c *)
Lemma c0_check_requests_pre : forall E regs m kbs mbs,
  lenv_ok E -> spZ regs = e_S E - SLOT_FRAME -> arg regs 0 = e_md E ->
  nlk_at m kbs -> model_at m (e_md E) mbs -> nlk_wf kbs -> model_wf mbs -> requests_are kbs mbs ->
  c0_check_requests_Pre regs m.
Proof.
  intros E regs m kbs mbs HE SP A0 NL MD NW MW RA.
  destruct HE as (HS1 & HS2 & _ & (D1 & D2 & D3) & _).
  pose proof (c0_img_free _ _ D3 ltac:(c0_unf; lia)) as DF.
  unfold c0_check_requests_Pre. exists kbs, mbs. cbv beta. rewrite A0.
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - unfold frame_apart_gnl, apart_gnl. rewrite SP. c0_unf; lia.
  - unfold apart_frame. rewrite SP. c0_unf; lia.
  - unfold apart_gnl. destruct DF; c0_unf; lia.
Qed.
