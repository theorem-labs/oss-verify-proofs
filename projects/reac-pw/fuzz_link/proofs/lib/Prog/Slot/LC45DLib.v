(* Piece d of the C45 brief (op_decide, 0x13a9c - 0x13af4): the lemmas the five segments c45_d0 .. c45_d4
   (LC45D.v, LC45D2.v) share.

   - d_fp_refl / d_fp_win: the footprint `seg_fp` of a segment that writes nothing, or only a window
     [lo, sp) of the stack;
   - d_split8 / d_join8: an 8-byte word cell cut off the front of a byte cell, and glued back;
   - dwin and the dc_* lemmas: every memory fact of op_decide's cuts survives a leaf call that munched
     only [lo, hi) with S - 65536 <= lo and hi <= sp (the frame, the buffers, the two strings text_of
     answered, g_nl, g_names, the image, the md / mk blocks, the payload, errno, task_mem). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC45Defs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The footprint
   ========================================================================== *)

Lemma d_fp_refl : forall S hp m, seg_fp S hp m m.
Proof.
  intros S hp m. exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
  intros x _ Ho. exfalso. apply Ho. exact I.
Qed.

Lemma d_fp_win : forall E m m' lo, e_S E - SLOT_STACK_Z <= lo ->
  munch [(lo, c45_sp E)] m m' -> wmono rsegs m m' -> seg_fp (e_S E) (c45_hp E) m m'.
Proof.
  intros E m m' lo Hlo MU WM. exists [(lo, c45_sp E)]. split; [exact MU|]. split; [exact WM|].
  intros x Hx Ho. left. cbn [outside] in Ho.
  assert (Hin : lo <= x < c45_sp E).
  { destruct (Z_le_gt_dec lo x); [destruct (Z_lt_ge_dec x (c45_sp E))|];
      first [lia | exfalso; apply Ho; split; [lia | exact I]]. }
  unfold c45_sp, SLOT_FRAME, SLOT_STACK_Z in *. lia.
Qed.

Lemma d_munch_sub : forall lo lo' hi m m', lo <= lo' -> munch [(lo', hi)] m m' -> munch [(lo, hi)] m m'.
Proof.
  intros lo lo' hi m m' H MU. apply (munch_weaken [(lo', hi)]); [|exact MU].
  intros x (Hx & _). split; [lia | exact I].
Qed.

(* ==========================================================================
   2. Word cells cut off and glued back
   ========================================================================== *)

Lemma d_le8_bytes : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite Z_to_le_bytes_mod by (cbn; lia). rewrite <- Hl. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

Lemma d_split8 : forall m A n j, (8 <= n)%nat -> rw_cells rsegs m A [CB n j] ->
  exists w j', rw_cells rsegs m A [C8 w] /\ rw_cells rsegs m (A + 8) [CB (n - 8) j'].
Proof.
  intros m A n j Hn [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes cells_size csize] in Hb, Hw. rewrite app_nil_r in Hb.
  exists (le_bytes_to_word (firstn 8 j)), (skipn 8 j).
  assert (L8 : length (firstn 8 j) = 8%nat) by (rewrite length_firstn; lia).
  rewrite <- (firstn_skipn 8 j) in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite L8 in B2. change (Z.of_nat 8) with 8 in B2.
  destruct Hw as (W1 & W2 & W3).
  unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite !app_nil_r. rewrite (d_le8_bytes _ L8).
  split.
  - split.
    + split; [split; exact I | exact B1].
    + split; [lia|]. split; [lia|]. intros i Hi. apply W3. lia.
  - split.
    + split; [split; [rewrite length_skipn; lia | exact I] | exact B2].
    + split; [lia|]. split; [lia|]. intros i Hi. replace (A + 8 + i) with (A + (8 + i)) by lia.
      apply W3. lia.
Qed.

Lemma d_join8 : forall m A w n j, rw_cells rsegs m A [C8 w] -> rw_cells rsegs m (A + 8) [CB n j] ->
  rw_cells rsegs m A [CB (8 + n) (le8 w ++ j)].
Proof.
  intros m A w n j [[_ B1] (P1 & P2 & P3)] [[Hwf B2] (Q1 & Q2 & Q3)].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes cells_size csize] in B1, B2, P2, P3, Q2, Q3. rewrite app_nil_r in B1, B2.
  unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r. split; [split|].
  - split; [rewrite length_app, length_le8; lia | exact I].
  - apply bytes_at_app. split; [exact B1|]. rewrite length_le8. exact B2.
  - split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_ge_dec i 8).
    + apply P3. lia.
    + replace (A + i) with (A + 8 + (i - 8)) by lia. apply Q3. lia.
Qed.

(* ==========================================================================
   3. The cursor, the kernel count, the placement
   ========================================================================== *)

Lemma d_cur_next : forall E P N, c45_cur E P N -> 1 <= N -> c45_cur E (P + 1) (N - 1).
Proof. intros E P N (k & Hk & HP & HN) H1. exists (k + 1). lia. Qed.

Lemma d_kmg_next : forall E i kbs mbs gbs m, 0 <= i -> c45_kmg E i kbs mbs gbs m -> c45_kmg E (i + 1) kbs mbs gbs m.
Proof.
  intros E i kbs mbs gbs m Hi (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj _ A8))))))). lia.
Qed.

Lemma d_env : forall E, lenv_ok E ->
  0x960e0 + 65536 <= e_S E /\ e_S E <= 2 ^ 47 /\
  e_md E + MD_SIZE <= e_S E - 65536 /\ e_mk E + MK_SIZE <= e_S E - 65536 /\
  e_p0 E + Z.of_nat (length (e_pl E)) <= e_S E - 65536.
Proof.
  intros E (S1 & S2 & _ & (M1 & M2 & _) & (K1 & K2 & _) & _ & _ & _ & _ & (P1 & P2 & _) & _).
  unfold SLOT_STACK_Z in *. lia.
Qed.

(* where a string text_of answered lies: below the stack window *)
Lemma d_loc_bound : forall E own s t, lenv_ok E -> c45_loc E own s t ->
  0 < s /\ s + Z.of_nat (length t) + 1 <= e_S E - 65536.
Proof.
  intros E own s t OK L. pose proof (d_env E OK) as EV.
  destruct L as [(_ & L1 & L2) | (_ & -> & k & K1 & K2 & K3 & K4)];
    unfold A_RO_LO, A_RO_END, SLOT_STACK_Z in *; lia.
Qed.

(* ==========================================================================
   4. Facts that survive a munched window [lo, hi) of the stack
   ========================================================================== *)

Definition dwin (E : lenv) (lo hi : Z) (m m' : word -> option byte) : Prop :=
  lenv_ok E /\ e_S E - 65536 <= lo /\ hi <= c45_sp E /\ munch [(lo, hi)] m m' /\ wmono rsegs m m'.

Lemma dw_img : forall E lo hi m m', dwin E lo hi m m' -> 0x960e0 <= lo.
Proof. intros E lo hi m m' (OK & LO & _). pose proof (d_env E OK) as EV. lia. Qed.

Lemma dc_bytes : forall E lo hi m m', dwin E lo hi m m' -> forall a bs, bytes_at rsegs m a bs ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m' a bs.
Proof.
  intros E lo hi m m' (_ & _ & _ & MU & _) a bs H D.
  eapply bytes_at_transport; [exact H | exact MU |]. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma dc_u8arr : forall E lo hi m m', dwin E lo hi m m' -> forall a bs, u8arr rsegs m a bs ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> u8arr rsegs m' a bs.
Proof.
  intros E lo hi m m' (_ & _ & _ & MU & WM) a bs H D.
  eapply u8arr_transport; [exact H | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma dc_cells : forall E lo hi m m', dwin E lo hi m m' -> forall a cs, rw_cells rsegs m a cs ->
  a + Z.of_nat (cells_size cs) <= lo \/ hi <= a -> rw_cells rsegs m' a cs.
Proof.
  intros E lo hi m m' (_ & _ & _ & MU & WM) a cs H D.
  eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma dc_cstr : forall E lo hi m m', dwin E lo hi m m' -> forall a s, cstr_at m a s ->
  a + Z.of_nat (length s) + 1 <= lo \/ hi <= a -> cstr_at m' a s.
Proof.
  intros E lo hi m m' DW a s [H N] D. split; [|exact N].
  apply (dc_bytes _ _ _ _ _ DW); [exact H|]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma dc_u64 : forall E lo hi m m', dwin E lo hi m m' -> forall a v, u64_at m a v ->
  a + 8 <= lo \/ hi <= a -> u64_at m' a v.
Proof.
  intros E lo hi m m' DW a v H D. unfold u64_at in *.
  apply (dc_bytes _ _ _ _ _ DW); [exact H|]. rewrite length_le8. lia.
Qed.

Lemma dc_u32 : forall E lo hi m m', dwin E lo hi m m' -> forall a v, u32_at m a v ->
  a + 4 <= lo \/ hi <= a -> u32_at m' a v.
Proof.
  intros E lo hi m m' DW a v H D. unfold u32_at in *.
  apply (dc_bytes _ _ _ _ _ DW); [exact H|]. rewrite length_le4. lia.
Qed.

Lemma dc_gnames : forall E lo hi m m', dwin E lo hi m m' -> gnames_at m -> gnames_at m'.
Proof.
  intros E lo hi m m' DW G k Hk. pose proof (dw_img _ _ _ _ _ DW) as IMG.
  destruct (G k Hk) as (rest & B & L). exists rest. split; [|exact L].
  apply (dc_bytes _ _ _ _ _ DW); [exact B|]. rewrite L. unfold A_G_NAMES. lia.
Qed.

Lemma d_odd_bound : forall i, (i < 6)%nat ->
  nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= 0x960e0.
Proof.
  intros i Hi. do 6 (destruct i as [|i]; [apply Z.leb_le; vm_compute; reflexivity|]). lia.
Qed.

Lemma dc_odd : forall E lo hi m m', dwin E lo hi m m' -> odd_at m -> odd_at m'.
Proof.
  intros E lo hi m m' DW O i Hi. destruct (O i Hi) as [U C]. pose proof (dw_img _ _ _ _ _ DW) as IMG.
  pose proof (d_odd_bound i Hi) as OB. split.
  - apply (dc_u64 _ _ _ _ _ DW); [exact U|]. unfold A_ODD. lia.
  - apply (dc_cstr _ _ _ _ _ DW); [exact C|]. lia.
Qed.

Lemma d_pol_bound :
  A_PREFIX + Z.of_nat (length S_PREFIX) + 1 <= 0x960e0 /\ A_SERVED + Z.of_nat (length S_SERVED) + 1 <= 0x960e0 /\
  A_VLAN + Z.of_nat (length S_VLAN) + 1 <= 0x960e0 /\ A_EMPTY + Z.of_nat (length (@nil byte)) + 1 <= 0x960e0.
Proof. repeat split; apply Z.leb_le; vm_compute; reflexivity. Qed.

Lemma dc_policy : forall E lo hi m m', dwin E lo hi m m' -> policy_ro m -> policy_ro m'.
Proof.
  intros E lo hi m m' DW (P1 & P2 & P3 & P4). pose proof (dw_img _ _ _ _ _ DW) as IMG.
  destruct d_pol_bound as (Q1 & Q2 & Q3 & Q4).
  split; [|split; [|split]]; (apply (dc_cstr _ _ _ _ _ DW); [eassumption | lia]).
Qed.

Lemma dc_la : forall E lo hi m m', dwin E lo hi m m' -> la_ok m -> la_ok m'.
Proof.
  intros E lo hi m m' DW (la & sl & C & B & L). exists la, sl. pose proof (dw_img _ _ _ _ _ DW) as IMG.
  split; [|split; [|exact L]].
  - apply (dc_cells _ _ _ _ _ DW); [exact C|].
    assert (SZ : Z.of_nat (cells_size [CB (Z.to_nat 300) la; C1 (zb 0)]) = 301) by reflexivity.
    rewrite SZ. unfold A_LONG_ALIAS. lia.
  - apply (dc_bytes _ _ _ _ _ DW); [exact B|]. rewrite L. unfold A_LONG_ALIAS, LONG_ALIAS_SIZE. lia.
Qed.

Lemma dc_texts : forall E lo hi m m', dwin E lo hi m m' -> texts_at m -> texts_at m'.
Proof.
  intros E lo hi m m' DW T i Hi. pose proof (dw_img _ _ _ _ _ DW) as IMG.
  apply (dc_u64 _ _ _ _ _ DW); [exact (T i Hi)|]. unfold A_TEXTS. lia.
Qed.

Lemma dc_ifptrs : forall E lo hi m m', dwin E lo hi m m' -> ifptrs_at m -> ifptrs_at m'.
Proof.
  intros E lo hi m m' DW T i Hi. pose proof (dw_img _ _ _ _ _ DW) as IMG.
  apply (dc_u64 _ _ _ _ _ DW); [exact (T i Hi)|]. unfold A_G_NL, NK_IF_NAME. lia.
Qed.

Lemma dc_guard : forall E lo hi m m', dwin E lo hi m m' -> guard_m m -> guard_m m'.
Proof.
  intros E lo hi m m' DW (G1 & c & G2). pose proof (dw_img _ _ _ _ _ DW) as IMG.
  split; [|exists c];
    (apply (dc_bytes _ _ _ _ _ DW); [eassumption|]); rewrite length_le8; unfold A_GOT_GUARD_S, A_GUARD_S; lia.
Qed.

Lemma dc_keep : forall E lo hi m m', dwin E lo hi m m' -> c45_keep E m -> c45_keep E m'.
Proof.
  intros E lo hi m m' DW (G & O & P & L & T & I & W & U & B).
  pose proof DW as (OK & LO & HI & MU & WM). pose proof (d_env E OK) as EV.
  split; [exact (dc_gnames _ _ _ _ _ DW G)|]. split; [exact (dc_odd _ _ _ _ _ DW O)|].
  split; [exact (dc_policy _ _ _ _ _ DW P)|]. split; [exact (dc_la _ _ _ _ _ DW L)|].
  split; [exact (dc_texts _ _ _ _ _ DW T)|]. split; [exact (dc_ifptrs _ _ _ _ _ DW I)|].
  split; [exact (wr_at_transport rsegs m m' A_ERRNO 4 W WM)|]. split; [exact (dc_guard _ _ _ _ _ DW U)|].
  apply (dc_bytes _ _ _ _ _ DW); [exact B|]. lia.
Qed.

(* the interface table: each name pointer is the one interfaces() stored (ifptrs_at), so its string lies
   in g_names or .rodata *)
Lemma d_link_len : length link_tab = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma d_link_bound : forall i nm ix, nth_error link_tab i = Some (nm, ix) ->
  (i < 64)%nat /\ 0 <= nth i link_ptrs 0 /\ nth i link_ptrs 0 + Z.of_nat (length nm) + 1 <= 0x960e0.
Proof.
  intros i nm ix H.
  assert (Hi : (i < 64)%nat).
  { rewrite <- d_link_len. apply nth_error_Some. rewrite H. discriminate. }
  assert (B : forallb (fun k => match nth_error link_tab k with
                                | Some (nm0, _) => (0 <=? nth k link_ptrs 0) &&
                                                   (nth k link_ptrs 0 + Z.of_nat (length nm0) + 1 <=? 0x960e0)
                                | None => true
                                end) (seq 0 64) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B i ltac:(apply in_seq; lia)). cbv beta in B.
  rewrite H in B. cbv iota in B. apply andb_true_iff in B. destruct B as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2. split; [exact Hi|]. split; lia.
Qed.

Lemma d_u64_same : forall m a p q, u64_at m a p -> u64_at m a q -> 0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> p = q.
Proof.
  intros m a p q (_ & _ & H1) (_ & _ & H2) Rp Rq.
  assert (E8 : le8 (wz p) = le8 (wz q)).
  { apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [Hi|Hi].
    - rewrite <- (H1 i ltac:(rewrite length_le8; lia)), <- (H2 i ltac:(rewrite length_le8; lia)). reflexivity.
    - rewrite !(proj2 (nth_error_None _ i)) by (rewrite length_le8; lia). reflexivity. }
  apply (f_equal le_bytes_to_word) in E8. rewrite !le_bytes_to_word_le8 in E8.
  unfold wz in E8. apply (f_equal (@bv_unsigned 64)) in E8. rewrite !unsigned_lit in E8 by lia. exact E8.
Qed.

Lemma dc_iftab : forall E lo hi m m', dwin E lo hi m m' -> forall kbs,
  ifptrs_at m -> iftab_at m kbs link_tab -> iftab_at m' kbs link_tab.
Proof.
  intros E lo hi m m' DW kbs IP (NI & NL & T). pose proof (dw_img _ _ _ _ _ DW) as IMG.
  split; [exact NI|]. split; [exact NL|].
  intros i nm ix Hi. destruct (T i nm ix Hi) as (R & p & U & P0 & C & U4). split; [exact R|].
  destruct (d_link_bound i nm ix Hi) as (Hi64 & Q0 & QB).
  assert (Ep : p = nth i link_ptrs 0).
  { apply (d_u64_same m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i)); [exact U | exact (IP i Hi64) | | lia].
    destruct C as [(C0 & C1 & _) _]. rewrite length_app in C1. cbn [length] in C1. lia. }
  exists p. split; [|split; [exact P0|split]].
  - apply (dc_u64 _ _ _ _ _ DW); [exact U|]. unfold A_G_NL, NK_IF_NAME. lia.
  - apply (dc_cstr _ _ _ _ _ DW); [exact C|]. subst p. lia.
  - apply (dc_u32 _ _ _ _ _ DW); [exact U4|]. unfold A_G_NL, NK_IF_INDEX. lia.
Qed.

Lemma dc_kmg : forall E lo hi m m', dwin E lo hi m m' -> forall i kbs mbs gbs,
  c45_keep E m -> c45_kmg E i kbs mbs gbs m -> c45_kmg E i kbs mbs gbs m'.
Proof.
  intros E lo hi m m' DW i kbs mbs gbs KP (NA & NW & IT & O1 & O2 & O3 & O4 & MA & MW & GA & GW & GR).
  pose proof (dw_img _ _ _ _ _ DW) as IMG. pose proof DW as (OK & LO & HI & MU & WM).
  pose proof (d_env E OK) as EV.
  destruct KP as (_ & _ & _ & _ & _ & IP & _).
  destruct NA as [NA NL]. destruct MA as [MA ML]. destruct GA as [GA GL].
  refine (conj (conj _ NL) (conj NW (conj _ (conj O1 (conj O2 (conj O3 (conj O4
           (conj (conj _ ML) (conj MW (conj (conj _ GL) (conj GW GR))))))))))).
  - apply (dc_u8arr _ _ _ _ _ DW); [exact NA|]. rewrite NL. unfold A_G_NL, NK_SIZE. lia.
  - exact (dc_iftab _ _ _ _ _ DW kbs IP IT).
  - apply (dc_u8arr _ _ _ _ _ DW); [exact MA|]. rewrite ML. lia.
  - apply (dc_u8arr _ _ _ _ _ DW); [exact GA|]. rewrite GL. lia.
Qed.

Lemma dc_frame : forall E lo hi m m', dwin E lo hi m m' -> forall j0 P N,
  c45_frame E j0 P N m -> c45_frame E j0 P N m'.
Proof.
  intros E lo hi m m' DW j0 P N (F1 & F2 & F3). pose proof DW as (_ & _ & HI & _ & _).
  split; [|split].
  - apply (dc_cells _ _ _ _ _ DW); [exact F1|]. lia.
  - apply (dc_cells _ _ _ _ _ DW); [exact F2|]. unfold FO_P. lia.
  - apply (dc_bytes _ _ _ _ _ DW); [exact F3|]. unfold c45_sp, SLOT_FRAME in HI. lia.
Qed.

Lemma dc_str : forall E lo hi m m', dwin E lo hi m m' -> forall own s t,
  c45_loc E own s t -> cstr_at m s t -> cstr_at m' s t.
Proof.
  intros E lo hi m m' DW own s t L C. pose proof DW as (OK & LO & _).
  pose proof (d_loc_bound E own s t OK L) as LB.
  apply (dc_cstr _ _ _ _ _ DW); [exact C|]. lia.
Qed.

Lemma dc_task : forall E lo hi m m', dwin E lo hi m m' -> stk rsegs m lo hi ->
  MemNorm.task_mem rsegs m -> MemNorm.task_mem rsegs m'.
Proof.
  intros E lo hi m m' DW (S0 & S1 & SK) T a b Ea. pose proof DW as (_ & _ & _ & MU & _).
  destruct (Z_le_gt_dec lo (bv_unsigned a)) as [A1|A1].
  - destruct (Z_lt_ge_dec (bv_unsigned a) hi) as [A2|A2].
    + destruct (SK (bv_unsigned a) (conj A1 A2)) as [_ (b0 & Hb0)].
      unfold wa in Hb0. rewrite Z_to_bv_lit_self in Hb0. unfold mrd in Hb0.
      destruct (m a) as [b1|] eqn:Ma; [exact (T a b1 Ma)|].
      left. unfold seg_rom, memory_read in Hb0. change (Z.of_N 1) with 1 in Hb0.
      destruct (find_segment rsegs (bv_unsigned a) 1) as [sg|]; [discriminate | discriminate Hb0].
    + rewrite (MU a) in Ea; [exact (T a b Ea)|]. cbn [outside]. split; [lia | exact I].
  - rewrite (MU a) in Ea; [exact (T a b Ea)|]. cbn [outside]. split; [lia | exact I].
Qed.

(* the window of a 16-byte leaf frame below sp *)
Lemma d_dwin16 : forall E m m', lenv_ok E -> munch [(c45_sp E - 16, c45_sp E)] m m' -> wmono rsegs m m' ->
  dwin E (c45_sp E - 16) (c45_sp E) m m'.
Proof.
  intros E m m' OK MU WM. pose proof (d_env E OK) as EV.
  split; [exact OK|]. split; [unfold c45_sp, SLOT_FRAME; lia|]. split; [lia|]. split; assumption.
Qed.

Lemma d_stk16 : forall E m, lenv_ok E -> stk rsegs m (e_S E - SLOT_STACK_Z) (c45_sp E) ->
  stk rsegs m (c45_sp E - 16) (c45_sp E).
Proof.
  intros E m OK ST. pose proof (d_env E OK) as EV.
  exact (proj2 (stk_split rsegs m (e_S E - SLOT_STACK_Z) (c45_sp E - 16) (c45_sp E) ST
                  ltac:(unfold c45_sp, SLOT_FRAME, SLOT_STACK_Z; lia))).
Qed.
