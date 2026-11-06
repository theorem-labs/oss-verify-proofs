(* Arm c2 (op_mark), piece HEAD: the facts the image's bytes give (vm_compute over rsegs, read through
   mem_inv) and the premises of kernel_c.v's contract they settle.
   1. where the heap blocks can be (pf_img_free: below 0x10000 or above the image, 0x97000);
   2. kernel_apart for the three kinds of address the kernel Pre names: the image below g_nl, g_names,
      a heap block below the stack window;
   3. the C string of selector s (c2_name_ok): g_names slots, the `odd` strings and their slack;
   4. the texts table premise and the interface-name premise of kernel_contract. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs LC2HeadA.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The image's reserved segments end at 0x97000
   ========================================================================== *)

Definition c2h_ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint c2h_cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => c2h_cov L' (if a <=? cur then Z.max cur b else cur) end.

Lemma c2h_cov_in : forall L cur x, cur <= x < c2h_cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [c2h_cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'.
      split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

Lemma c2h_rsegs_pages : c2h_cov (c2h_ivs (segments_reserved rsegs)) 0x10000 = 0x97000.
Proof. vm_compute. reflexivity. Qed.

Lemma c2h_img_free_bound : forall D n, 0 <= D -> 0 < n -> pf_img_free D n -> D + n <= 0x10000 \/ 0x97000 <= D.
Proof.
  intros D n HD Hn F.
  assert (C : forall x, 0x10000 <= x < 0x97000 -> exists s, In s (segments_reserved rsegs)
                /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros x Hx. rewrite <- c2h_rsegs_pages in Hx. destruct (c2h_cov_in _ _ _ Hx) as (a & b & Hin & Hab).
    unfold c2h_ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s & Es & Hs). injection Es as Ea Eb.
    exists s. split; [exact Hs | lia]. }
  destruct (Z.lt_ge_cases D 0x10000) as [H1|H1].
  - destruct (Z.le_gt_cases (D + n) 0x10000) as [H2|H2]; [left; exact H2|].
    destruct (C 0x10000 ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F (0x10000 - D) ltac:(lia) s Hs). replace (D + (0x10000 - D)) with 0x10000 by lia. exact Hx.
  - destruct (Z.lt_ge_cases D 0x97000) as [H2|H2]; [|right; exact H2].
    destruct (C D ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F 0 ltac:(lia) s Hs). rewrite Z.add_0_r. exact Hx.
Qed.

(* a block of lenv_ok (blk_out) is below 0x10000 or above the image, and below the stack window *)
Lemma c2h_blk_where : forall S a n, 0 < n -> blk_out S a n ->
  4096 <= a /\ a + n <= S - SLOT_STACK_Z /\ (a + n <= 0x10000 \/ 0x97000 <= a).
Proof.
  intros S a n Hn (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  apply (c2h_img_free_bound a n); [lia | exact Hn | exact H3].
Qed.

(* ==========================================================================
   2. kernel_apart
   ========================================================================== *)

(* the registers of the kernel call: sp = S - 480 with lenv_ok's S, a0 = sp + 0x40 *)
Definition c2h_kregs (regs : bvmap 5 word) : Prop :=
  0x960e0 + 65536 - 480 <= spZ regs /\ spZ regs <= 2 ^ 47 /\ arg regs 0 = spZ regs + 64.

Lemma c2h_kapart_lo : forall regs a n, c2h_kregs regs -> 0 <= n -> a + n <= A_G_NL -> kernel_apart regs a n.
Proof.
  intros regs a n (R1 & R2 & R3) Hn Ha. unfold kernel_apart, apart_frame, apart_gnl.
  unfold A_G_NL, A_LONG_ALIAS, LONG_ALIAS_SIZE in *. lia.
Qed.

Lemma c2h_kapart_gn : forall regs a n, c2h_kregs regs -> 0 <= n -> A_G_NAMES <= a -> a + n <= A_LONG_ALIAS ->
  kernel_apart regs a n.
Proof.
  intros regs a n (R1 & R2 & R3) Hn Ha1 Ha2. unfold kernel_apart, apart_frame, apart_gnl.
  unfold A_G_NL, NK_SIZE, A_G_NAMES, A_LONG_ALIAS, LONG_ALIAS_SIZE in *. lia.
Qed.

Lemma c2h_kapart_heap : forall regs a n, c2h_kregs regs -> 0 <= n -> 0 <= a ->
  a + n <= spZ regs + 480 - SLOT_STACK_Z -> (a + n <= 0x10000 \/ 0x97000 <= a) -> kernel_apart regs a n.
Proof.
  intros regs a n (R1 & R2 & R3) Hn Ha1 Ha2 Ha3. unfold kernel_apart, apart_frame, apart_gnl.
  unfold A_G_NL, NK_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE, SLOT_STACK_Z in *. lia.
Qed.

(* ==========================================================================
   3. The name of selector s (c2_name_ok)
   ========================================================================== *)

Lemma c2h_zb_ne0 : forall x, 0 < x < 256 -> zb x <> zb 0.
Proof.
  intros x Hx E. apply (f_equal bv_unsigned) in E. unfold zb in E. rewrite !Z_to_bv_unsigned in E.
  unfold bv_wrap in E. change (bv_modulus 8) with 256 in E. rewrite !Z.mod_small in E by lia. lia.
Qed.

Lemma c2h_gname_nonul : forall s, 0 <= s < 64 -> ~ In (zb 0) (gname s).
Proof.
  intros s Hs H. unfold gname, gname_z in H. apply in_map_iff in H. destruct H as (x & Ex & Hx).
  assert (Rx : 0 < x < 256).
  { unfold dec2 in Hx. destruct (s <? 10) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
      cbn [In] in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x;
      first [lia | Z.div_mod_to_equations; lia]. }
  exact (c2h_zb_ne0 x Rx Ex).
Qed.

Lemma c2h_gname_len : forall s, 0 <= s < 64 -> (3 <= length (gname s) <= 4)%nat.
Proof.
  intros s Hs. unfold gname, gname_z, dec2. rewrite length_map.
  destruct (s <? 10); cbn [length]; lia.
Qed.

(* the slack bytes after a C string of the image: up to the next multiple of 8 *)
Definition c2h_slack (a : Z) : list byte :=
  match image_bytes rsegs a (Z.to_nat ((- a) mod 8)) with Some l => l | None => [] end.

Definition c2h_odd_ok2 (j : nat) : bool :=
  let p := nth j odd_ptrs 0 in
  let t := nth j odd_strs [] in
  let a := p + Z.of_nat (length t) + 1 in
  Nat.leb (length t) 11 && (A_RO_LO <=? p) && (p + 16 <=? A_RO_END) && negb (p =? 0) &&
  ro_bytes_b rsegs a (c2h_slack a) && (Z.of_nat (length (c2h_slack a)) =? (- a) mod 8).
Lemma c2h_odd_all2 : forallb c2h_odd_ok2 (seq 0 6) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c2h_name_ok : forall m s, gnames_at m -> odd_at m -> mem_inv rsegs m -> 0 <= s <= 255 -> c2_name_ok m s.
Proof.
  intros m s HG HO MI Hs. unfold c2_name_ok.
  destruct (Z.eq_dec s 255) as [E255|N255]; [|destruct (Z_lt_dec s 64) as [Lo|Hi]].
  - subst s. split; [reflexivity|]. intros t Ht. discriminate Ht.
  - rewrite (c2h_sel_name_lo s ltac:(lia)), (c2h_sel_ptr_lo s ltac:(lia)).
    destruct (HG s ltac:(lia)) as (rest & B & L).
    pose proof (c2h_gname_len s ltac:(lia)) as GL.
    assert (B' : bytes_at rsegs m (A_G_NAMES + 8 * s) ((gname s ++ [zb 0]) ++ rest))
      by (rewrite <- app_assoc; exact B).
    split.
    + split; [unfold A_G_NAMES; lia|]. split; [exact (c2h_bytes_at_prefix _ _ _ _ B') | exact (c2h_gname_nonul s ltac:(lia))].
    + intros t Ht. injection Ht as <-. split; [lia|]. split; [right; exists s; split; [lia | split; [reflexivity | lia]]|].
      exists rest. pose proof (c2h_bytes_at_suffix _ _ _ _ B') as B2.
      rewrite length_app in B2. cbn [length] in B2. rewrite Nat2Z.inj_add in B2.
      replace (A_G_NAMES + 8 * s + (Z.of_nat (length (gname s)) + Z.of_nat 1))
        with (A_G_NAMES + 8 * s + Z.of_nat (length (gname s)) + 1) in B2 by lia.
      split; [exact B2|].
      rewrite length_app in L. cbn [length] in L.
      unfold A_G_NAMES. Z.div_mod_to_equations. lia.
  - assert (Hj : (Z.to_nat (s mod 6) < 6)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; cbn; lia).
    rewrite (c2h_sel_name_hi s ltac:(lia) N255), (c2h_sel_ptr_hi s ltac:(lia) N255).
    remember (Z.to_nat (s mod 6)) as j eqn:Ej.
    pose proof (c2h_forallb_seq _ _ _ c2h_odd_all2 Hj) as K. unfold c2h_odd_ok2 in K.
    repeat (apply andb_true_iff in K; destruct K as [K ?]).
    rename K into K1.
    match goal with
    | H1 : (A_RO_LO <=? _) = true, H2 : (_ + 16 <=? A_RO_END) = true, H3 : negb (_ =? 0) = true,
      H4 : ro_bytes_b rsegs _ _ = true, H5 : (Z.of_nat (length _) =? _) = true |- _ =>
        apply Z.leb_le in H1, H2; apply negb_true_iff, Z.eqb_neq in H3; apply Z.eqb_eq in H5;
        rename H1 into K2, H2 into K3, H3 into K4, H4 into K5, H5 into K6
    end.
    apply Nat.leb_le in K1.
    destruct (HO j Hj) as [_ C].
    split; [split; [exact K4 | exact C]|].
    intros t Ht. assert (Et : nth j odd_strs [] = t) by congruence. subst t.
    split; [exact K1|]. split; [left; split; assumption|].
    eexists. split; [|exact K6].
    apply ro_bytes_at; [exact MI | | | apply ro_bytes_b_sound; exact K5].
    + unfold A_RO_LO in K2. lia.
    + rewrite K6. unfold A_RO_END in K3. Z.div_mod_to_equations. lia.
Qed.

(* ==========================================================================
   4. The kernel Pre: the texts table and the interface names
   ========================================================================== *)

(* the C string of the image at a (fuel bounds its length) *)
Fixpoint c2h_img_str (a : Z) (fuel : nat) : list byte :=
  match fuel with
  | O => []
  | S f => match seg_rom rsegs (wa a) with
           | Some b => if bz b =? 0 then [] else b :: c2h_img_str (a + 1) f
           | None => []
           end
  end.

Definition c2h_text_ok (p : Z) : bool :=
  let s := c2h_img_str p 64 in
  let a := p + Z.of_nat (length s) + 1 in
  ro_bytes_b rsegs p (s ++ zb 0 :: c2h_slack a) && forallb (fun b => negb (bz b =? 0)) s &&
  ((- a) mod 8 <=? Z.of_nat (length (c2h_slack a))) && (Z.of_nat (length s) <? 4096) &&
  (0x10000 <=? p) && (a + Z.of_nat (length (c2h_slack a)) <=? A_RO_END).
Lemma c2h_texts_all : forallb c2h_text_ok texts_ptrs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c2h_texts_pre : forall regs m, c2h_kregs regs -> texts_at m -> mem_inv rsegs m ->
  forall i, 0 <= i < TEXTS_N -> exists p s slack,
    u64_at m (A_TEXTS + 8 * i) p /\ p <> 0
    /\ bytes_at rsegs m p (s ++ zb 0 :: slack) /\ ~ In (zb 0) s
    /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ Z.of_nat (length s) < NL_CHUNK_MAX
    /\ kernel_apart regs p (Z.of_nat (length s) + 1 + Z.of_nat (length slack)).
Proof.
  intros regs m KR HT MI i Hi. unfold TEXTS_N in Hi.
  set (j := Z.to_nat i).
  assert (Hj : (j < 11)%nat) by (unfold j; lia).
  set (p := nth j texts_ptrs 0).
  pose proof c2h_texts_all as A. rewrite forallb_forall in A.
  assert (Inp : In p texts_ptrs) by (apply nth_In; exact Hj).
  specialize (A p Inp). unfold c2h_text_ok in A.
  repeat (apply andb_true_iff in A; destruct A as [A ?]).
  match goal with
  | H2 : forallb _ _ = true, H3 : (_ mod 8 <=? _) = true, H4 : (_ <? 4096) = true,
    H5 : (0x10000 <=? _) = true, H6 : (_ <=? A_RO_END) = true |- _ =>
      rename H2 into A2, H3 into A3, H4 into A4, H5 into A5, H6 into A6
  end.
  apply Z.leb_le in A3, A5, A6. apply Z.ltb_lt in A4.
  exists p, (c2h_img_str p 64), (c2h_slack (p + Z.of_nat (length (c2h_img_str p 64)) + 1)).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - replace i with (Z.of_nat j) by (unfold j; lia). exact (HT j Hj).
  - lia.
  - apply ro_bytes_at; [exact MI | lia | | apply ro_bytes_b_sound; exact A].
    rewrite length_app. cbn [length]. unfold A_RO_END in A6. lia.
  - intros H. rewrite forallb_forall in A2. specialize (A2 _ H). cbn in A2. discriminate A2.
  - exact A3.
  - unfold NL_CHUNK_MAX. lia.
  - apply c2h_kapart_lo; [exact KR | lia | unfold A_RO_END, A_G_NL in *; lia].
Qed.

Lemma c2h_iface_pre : forall regs m kbs, c2h_kregs regs -> iftab_at m kbs link_tab -> ifptrs_at m ->
  forall tab i nm ix p, iftab_at m kbs tab -> nth_error tab i = Some (nm, ix) ->
    u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
    kernel_apart regs p (Z.of_nat (length nm) + 1).
Proof.
  intros regs m kbs KR (Ln & _ & HL) HP tab i nm ix p (Tn & _ & HT) Hnth U.
  assert (Hi : (i < 64)%nat).
  { rewrite c2h_link_tab_len in Ln. rewrite Ln in Tn.
    assert (i < length tab)%nat by (apply nth_error_Some; congruence). lia. }
  destruct (nth_error link_tab i) as [[nm2 ix2]|] eqn:E2.
  2:{ exfalso. apply nth_error_None in E2. rewrite c2h_link_tab_len in E2. lia. }
  destruct (HT i nm ix Hnth) as (_ & p1 & U1 & _ & C1 & _).
  destruct (HL i nm2 ix2 E2) as (_ & p2 & U2 & _ & C2 & _).
  assert (R1 : 0 <= p1 < 2 ^ 64).
  { destruct C1 as [B _]. pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite length_app in BB. cbn [length] in BB. lia. }
  assert (R2 : 0 <= p2 < 2 ^ 64).
  { destruct C2 as [B _]. pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite length_app in BB. cbn [length] in BB. lia. }
  pose proof (c2h_ifname_at m i p1 HP Hi U1 R1 nm2 ix2 E2) as E1.
  pose proof (c2h_ifname_at m i p2 HP Hi U2 R2 nm2 ix2 E2) as E3.
  subst p1 p2.
  pose proof (c2h_cstr_unique _ _ _ _ C1 C2) as Enm. subst nm2.
  pose proof (c2h_u64_unique _ _ _ _ U (HP i Hi)) as Ep.
  destruct (c2h_link_where i nm ix2 E2) as (_ & R).
  remember (nth i link_ptrs 0) as q eqn:Eq. clear Eq.
  destruct KR as (K1 & K2 & K3).
  unfold kernel_apart, apart_frame, apart_gnl. rewrite K3.
  unfold A_RO_END, A_G_NAMES, A_G_NL, NK_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE in *.
  rewrite (Z.mod_small q) in Ep by lia.
  Z.div_mod_to_equations. lia.
Qed.
