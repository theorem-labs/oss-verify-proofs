(* The op_unmark arm (c3) of LLVMFuzzerTestOneInput, plain image: generic tools its walk uses.
   - the ms_eqv closure (LDefs.eqv_cl) and how evt composes through it;
   - `leaf_run`: a call of a `leaf` contract from an mkR state, continued on the canonical mkR state
     (RegisterBridge.canonical_contract_transport), so the Step tactics keep working after the call;
   - the footprint the arm writes (c3_W) and its seg_fp;
   - rw_cells split / join, and 32-bit fields of a byte block (u8arr) read and written in place. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The ms_eqv closure
   ========================================================================== *)

Lemma c3_xregs_eqv_trans : forall R1 R2 R3,
  Regs6ss.xregs_eqv R1 R2 -> Regs6ss.xregs_eqv R2 R3 -> Regs6ss.xregs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. rewrite (H1 r Hr). exact (H2 r Hr). Qed.

Lemma c3_ms_eqv_trans : forall a b c, Regs6ss.ms_eqv a b -> Regs6ss.ms_eqv b c -> Regs6ss.ms_eqv a c.
Proof.
  intros a b c (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  split; [exact (c3_xregs_eqv_trans _ _ _ A1 B1)|].
  repeat split; congruence.
Qed.

Lemma c3_ms_eqv_refl : forall a, Regs6ss.ms_eqv a a.
Proof. intros a. split; [intros r _; reflexivity|]. repeat split; reflexivity. Qed.

Lemma eqv_cl_intro : forall (Q : machine_state -> Prop) ms, Q ms -> eqv_cl Q ms.
Proof. intros Q ms H. exists ms. split; [exact H | apply c3_ms_eqv_refl]. Qed.

Lemma eqv_cl_eqv : forall Q c a, eqv_cl Q c -> Regs6ss.ms_eqv c a -> eqv_cl Q a.
Proof. intros Q c a (c0 & H & E0) E. exists c0. split; [exact H | exact (c3_ms_eqv_trans _ _ _ E0 E)]. Qed.

Lemma eqv_cl_mono : forall (P Q : machine_state -> Prop) ms,
  (forall c, P c -> Q c) -> eqv_cl P ms -> eqv_cl Q ms.
Proof. intros P Q ms H (c & HP & E). exists c. split; [exact (H c HP) | exact E]. Qed.

(* run a piece stated on canonical states from any state eqv to one *)
Lemma evt_eqv_bind : forall (P Q : machine_state -> Prop),
  (forall c, P c -> evt rsegs (eqv_cl Q) c) -> forall ms, eqv_cl P ms -> evt rsegs (eqv_cl Q) ms.
Proof.
  intros P Q H ms (c & HP & E).
  pose proof (RegisterBridge.evt_register_transport rsegs _ c ms E (H c HP)) as K.
  eapply evt_mono; [exact K|]. intros a (c' & HQ & E'). exact (eqv_cl_eqv _ _ _ HQ E').
Qed.

Lemma evt_eqv_cut : forall (P Q : machine_state -> Prop) ms,
  evt rsegs (eqv_cl P) ms -> (forall c, P c -> evt rsegs (eqv_cl Q) c) -> evt rsegs (eqv_cl Q) ms.
Proof. intros P Q ms H K. eapply evt_cut; [exact H|]. apply evt_eqv_bind. exact K. Qed.

Lemma evt_eqv_done : forall (Q : machine_state -> Prop) ms, Q ms -> evt rsegs (eqv_cl Q) ms.
Proof. intros Q ms H. apply evt_done, eqv_cl_intro, H. Qed.

(* ==========================================================================
   2. A leaf call, continued on the canonical state
   ========================================================================== *)

Lemma leaf_run : forall pc K Pre Wr Post (Q : machine_state -> Prop),
  leaf pc K Pre Wr Post ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  Pre (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + K <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
  (forall (regs' : bvmap 5 word) (m' : word -> option byte),
     munch ((bv_unsigned sp - K, bv_unsigned sp)
              :: Wr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m)
           m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
     Post (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m regs' m' ->
     evt rsegs (eqv_cl Q)
       (MS (mkR (reg_get regs' 1) sp gp tp (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) s0 s1
                (reg_get regs' 10) (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13) (reg_get regs' 14)
                (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31))
           F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs (eqv_cl Q)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros pc K Pre Wr Post Q HL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m lo HP MI ST LO SP K'.
  specialize (HL _ F fc m lo HP MI ST LO SP).
  eapply evt_cut; [exact HL|].
  intros ms' (regs' & m' & -> & RP & MU & WM & MI' & ST' & PO).
  change (spZ (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
    with (bv_unsigned sp) in MU, ST'.
  change (getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 1)
    with ra.
  assert (R2 : reg_get regs' 2 = sp) by exact (RP 2 ltac:(cbv [callee_saved]; lia)).
  assert (R3 : reg_get regs' 3 = gp) by exact (RP 3 ltac:(cbv [callee_saved]; lia)).
  assert (R4 : reg_get regs' 4 = tp) by exact (RP 4 ltac:(cbv [callee_saved]; lia)).
  assert (R8 : reg_get regs' 8 = s0) by exact (RP 8 ltac:(cbv [callee_saved]; lia)).
  assert (R9 : reg_get regs' 9 = s1) by exact (RP 9 ltac:(cbv [callee_saved]; lia)).
  assert (R18 : reg_get regs' 18 = s2) by exact (RP 18 ltac:(cbv [callee_saved]; lia)).
  assert (R19 : reg_get regs' 19 = s3) by exact (RP 19 ltac:(cbv [callee_saved]; lia)).
  assert (R20 : reg_get regs' 20 = s4) by exact (RP 20 ltac:(cbv [callee_saved]; lia)).
  assert (R21 : reg_get regs' 21 = s5) by exact (RP 21 ltac:(cbv [callee_saved]; lia)).
  assert (R22 : reg_get regs' 22 = s6) by exact (RP 22 ltac:(cbv [callee_saved]; lia)).
  assert (R23 : reg_get regs' 23 = s7) by exact (RP 23 ltac:(cbv [callee_saved]; lia)).
  assert (R24 : reg_get regs' 24 = s8) by exact (RP 24 ltac:(cbv [callee_saved]; lia)).
  assert (R25 : reg_get regs' 25 = s9) by exact (RP 25 ltac:(cbv [callee_saved]; lia)).
  assert (R26 : reg_get regs' 26 = s10) by exact (RP 26 ltac:(cbv [callee_saved]; lia)).
  assert (R27 : reg_get regs' 27 = s11) by exact (RP 27 ltac:(cbv [callee_saved]; lia)).
  pose proof (RegisterBridge.canonical_contract_transport rsegs (eqv_cl Q)
                (MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs))) as T.
  eapply evt_mono; [apply T|].
  2:{ intros a (c & HQ & E). exact (eqv_cl_eqv _ _ _ HQ E). }
  change (evt rsegs (eqv_cl Q) (MS (Regs6ss.mkR_of regs') F (ret_pc ra) fc None m' (seg_rom rsegs))).
  unfold Regs6ss.mkR_of.
  rewrite R2, R3, R4, R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27.
  exact (K' regs' m' MU WM MI' ST' PO).
Qed.

(* the caller's footprint grows by what a callee wrote, when that lies inside it *)
Lemma munch_extend : forall W W' m0 m m', munch W m0 m -> munch W' m m' -> sub_fp W' W -> munch W m0 m'.
Proof. intros W W' m0 m m' H1 H2 Hs. exact (munch_trans W m0 m m' H1 (munch_weaken W' W m m' Hs H2)). Qed.

(* ==========================================================================
   3. The arm's footprint
   ========================================================================== *)

Definition c3_W (E : lenv) : list ivl :=
  [(e_S E - SLOT_STACK_Z, e_S E); (A_G_NL, A_G_NL + NK_SIZE); (A_LONG_ALIAS, A_LONG_ALIAS + LONG_ALIAS_SIZE);
   (A_ERRNO, A_ERRNO + 4); (e_md E, e_md E + MD_SIZE); (e_mk E, e_mk E + MK_SIZE)].

Definition c3_hp (E : lenv) : list (Z * Z) := [(e_md E, MD_SIZE); (e_mk E, MK_SIZE)].

Lemma c3_not_outside : forall W x, ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
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

Lemma c3_seg_fp : forall E m0 m', munch (c3_W E) m0 m' -> wmono rsegs m0 m' ->
  seg_fp (e_S E) (c3_hp E) m0 m'.
Proof.
  intros E m0 m' MU WM. exists (c3_W E). split; [exact MU|]. split; [exact WM|].
  intros x Hx HO. destruct (c3_not_outside _ _ HO) as (lo & hi & Hin & Hr).
  unfold c3_W in Hin. unfold own_w, c3_hp.
  cbn [In] in Hin.
  destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; inversion E1; subst lo hi.
  - left; lia.
  - right; left; lia.
  - right; right; right; left; lia.
  - right; right; right; right; left; lia.
  - right; right; right; right; right. exists (e_md E), MD_SIZE. split; [left; reflexivity | lia].
  - right; right; right; right; right. exists (e_mk E), MK_SIZE. split; [right; left; reflexivity | lia].
Qed.

Lemma c3_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
    + right. intros [H3 _]. apply H3. lia.
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
  - right. intros [_ H3]. exact (H H3).
Qed.

(* task_mem survives writes that stay inside the task's address space *)
Lemma c3_task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> x < TASK_SIZE) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' HT MU HW a b Ha. pose proof (bv_unsigned_in_range 64 a) as Ra.
  change (bv_modulus 64) with (2 ^ 64) in Ra.
  destruct (c3_outside_dec W (bv_unsigned a)) as [HO|HO].
  - rewrite (MU a HO) in Ha. exact (HT a b Ha).
  - right. exact (HW _ Ra HO).
Qed.

(* ==========================================================================
   4. Cell lists split and joined
   ========================================================================== *)

Lemma c3_wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2) <-> wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. split.
  - intros (Ha & Hn & H). split; (split; [lia|]; split; [lia|]); intros i Hi.
    + apply H. lia.
    + replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros [(Ha & Hn & H) (Hb & Hm & H')]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_dec i n1); [apply H; lia|].
    replace (A + i) with (A + n1 + (i - n1)) by lia. apply H'. lia.
Qed.

Lemma c3_rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  pose proof (cells_wf_app cs1 cs2) as WA.
  split.
  - intros [[W12 HB] HW]. apply WA in W12. destruct W12 as [W1 W2].
    apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [B1 B2].
    rewrite cells_bytes_length in B2 by exact W1.
    apply (proj1 (c3_wr_at_app m A _ _ (Nat2Z.is_nonneg (cells_size cs1)) (Nat2Z.is_nonneg (cells_size cs2)))) in HW.
    destruct HW as [H1 H2].
    exact (conj (conj (conj W1 B1) H1) (conj (conj W2 B2) H2)).
  - intros [[[W1 B1] H1] [[W2 B2] H2]].
    split; [split; [apply WA; split; assumption|]|].
    + apply (proj2 (bytes_at_app rsegs _ _ _ _)). split; [exact B1|].
      rewrite cells_bytes_length by exact W1. exact B2.
    + apply (proj2 (c3_wr_at_app m A _ _ (Nat2Z.is_nonneg (cells_size cs1)) (Nat2Z.is_nonneg (cells_size cs2)))).
      split; assumption.
Qed.

(* ==========================================================================
   5. A 32-bit field of a byte block, read and written in place
   ========================================================================== *)

Lemma c3_le4_slice : forall bs off, 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
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

Lemma c3_u8arr_rd32 : forall m A bs off a, u8arr rsegs m A bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  a = A + off -> ov_read_bytes rsegs m (Z_to_bv 64 a) 4 = Some (le4 (wz (fld_u32 bs off))).
Proof.
  intros m A bs off a [HB _] H0 H4 ->. rewrite c3_le4_slice by lia.
  exact (bytes_at_read rsegs m A bs off 4 HB H0 ltac:(lia)).
Qed.

Lemma c3_u8arr_store_ok : forall m A bs off a (n : nat), u8arr rsegs m A bs -> 0 <= off ->
  off + Z.of_nat n <= Z.of_nat (length bs) -> a = A + off -> store_ok rsegs m (Z_to_bv 64 a) n = true.
Proof. intros m A bs off a n [_ HW] H0 H4 ->. exact (wr_at_store_ok rsegs m A _ off n HW H0 H4). Qed.

Lemma c3_u8arr_write : forall m A bs off a xs, u8arr rsegs m A bs -> 0 <= off ->
  off + Z.of_nat (length xs) <= Z.of_nat (length bs) -> a = A + off ->
  u8arr rsegs (write_to_mem m (Z_to_bv 64 a) xs) A (upd_bytes bs (Z.to_nat off) xs).
Proof.
  intros m A bs off a xs [HB HW] H0 H4 ->. split.
  - exact (bytes_at_write_inside rsegs m A bs off xs HB H0 ltac:(lia)).
  - rewrite upd_bytes_length by lia. exact (wr_at_write rsegs m A _ _ xs HW).
Qed.

Lemma c3_upd_length : forall bs k xs, (k + length xs <= length bs)%nat -> length (upd_bytes bs k xs) = length bs.
Proof. intros. apply upd_bytes_length. exact H. Qed.

Lemma c3_slice_upd_same : forall bs k xs, (k + length xs <= length bs)%nat ->
  slice (upd_bytes bs k xs) (Z.of_nat k) (Z.of_nat (length xs)) = xs.
Proof.
  intros bs k xs H. unfold slice, upd_bytes. rewrite !Nat2Z.id.
  rewrite skipn_app, length_firstn, (Nat.min_l k (length bs)) by lia.
  rewrite skipn_all2 by (rewrite length_firstn; lia). rewrite Nat.sub_diag. cbn [app skipn].
  change (skipn 0 (xs ++ skipn (k + length xs) bs)) with (xs ++ skipn (k + length xs) bs).
  rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r.
Qed.

Lemma c3_slice_upd_other : forall bs k xs off n, (k + length xs <= length bs)%nat -> 0 <= off -> 0 <= n ->
  (off + n <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length xs) <= off) ->
  slice (upd_bytes bs k xs) off n = slice bs off n.
Proof.
  intros bs k xs off n H H0 H1 [Hb|Ha]; unfold slice, upd_bytes.
  - rewrite skipn_app, length_firstn, (Nat.min_l k (length bs)) by lia.
    rewrite firstn_app, length_skipn, length_firstn, (Nat.min_l k (length bs)) by lia.
    replace (Z.to_nat n - (k - Z.to_nat off))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
    rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
  - rewrite skipn_app, length_firstn, (Nat.min_l k (length bs)) by lia.
    rewrite skipn_all2 by (rewrite length_firstn; lia). cbn [app].
    rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
    rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma c3_fld_u32_upd_same : forall bs k v, (k + 4 <= length bs)%nat ->
  fld_u32 (upd_bytes bs k (le4 v)) (Z.of_nat k) = bv_unsigned v mod 2 ^ 32.
Proof.
  intros bs k v H. unfold fld_u32, link_spec.rdn.
  pose proof (c3_slice_upd_same bs k (le4 v) ltac:(rewrite length_le4; lia)) as HS.
  rewrite length_le4 in HS. change (Z.of_nat 4) with 4 in HS. rewrite HS.
  apply bytes_le_to_Z_le4.
Qed.

Lemma c3_rdn_upd_other : forall bs k xs off n, (k + length xs <= length bs)%nat -> 0 <= off -> 0 <= n ->
  (off + n <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length xs) <= off) ->
  link_spec.rdn (upd_bytes bs k xs) off n = link_spec.rdn bs off n.
Proof. intros. unfold link_spec.rdn. rewrite c3_slice_upd_other by assumption. reflexivity. Qed.

(* ==========================================================================
   6. Heap blocks against the image, and small byte facts
   ========================================================================== *)

(* the four loaded segments of the plain image are [0x10000, 0x97000) without a gap, so a block outside
   them (blk_out's pf_img_free) lies wholly below or wholly above the image *)
Lemma c3_img_free : forall a n, pf_img_free a n -> 1 <= n -> a + n <= 0x10000 \/ 0x97000 <= a.
Proof.
  intros a n H Hn.
  destruct (Z_le_dec (a + n) 0x10000) as [L|L]; [left; exact L|].
  destruct (Z_le_dec 0x97000 a) as [R|R]; [right; exact R|].
  exfalso.
  assert (HL : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)
               = [(65536, 8192); (73728, 57344); (131072, 4096); (135168, 483328)]) by (vm_compute; reflexivity).
  unfold pf_img_free in H.
  remember (segments_reserved rsegs) as l eqn:El. clear El.
  destruct l as [|s1 [|s2 [|s3 [|s4 [|s5 l]]]]]; cbn [map] in HL; try discriminate HL.
  injection HL as E1 F1 E2 F2 E3 F3 E4 F4.
  set (y := Z.max a 0x10000).
  assert (Hy : 0 <= y - a < n) by lia.
  replace (a + (y - a)) with y in H by lia.
  destruct (Z_lt_dec y 0x12000) as [Y1|Y1]; [apply (H (y - a) Hy s1); [left; reflexivity | lia]|].
  destruct (Z_lt_dec y 0x20000) as [Y2|Y2]; [apply (H (y - a) Hy s2); [right; left; reflexivity | lia]|].
  destruct (Z_lt_dec y 0x21000) as [Y3|Y3]; [apply (H (y - a) Hy s3); [right; right; left; reflexivity | lia]|].
  apply (H (y - a) Hy s4); [right; right; right; left; reflexivity | lia].
Qed.

Lemma c3_blk_img : forall S a n, blk_out S a n -> 1 <= n -> a + n <= 0x10000 \/ 0x97000 <= a.
Proof. intros S a n (_ & _ & H) Hn. exact (c3_img_free a n H Hn). Qed.

(* two byte lists read at the same address are equal *)
Lemma c3_bytes_at_same : forall m a l1 l2, bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 ->
  length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) HL. apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (length l1)) as [Hk|Hk].
  - rewrite <- (H1 k Hk), <- (H2 k ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 k) Hk), (proj2 (nth_error_None l2 k) ltac:(lia)). reflexivity.
Qed.

Lemma c3_le8_inj : forall v1 v2 : word, le8 v1 = le8 v2 -> v1 = v2.
Proof. intros v1 v2 H. rewrite <- (le_bytes_to_word_le8 v1), <- (le_bytes_to_word_le8 v2), H. reflexivity. Qed.

(* the bytes of a suffix of a list, at its offset *)
Lemma c3_bytes_at_skipn : forall m a bs k, bytes_at rsegs m a bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k HB Hk. rewrite <- (firstn_skipn k bs) in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by exact Hk. exact HB.
Qed.

(* one byte read through bytes_at *)
Lemma c3_byte_read : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros m a b H. pose proof (bytes_at_read rsegs m a [b] 0 1 H ltac:(lia) ltac:(cbn; lia)) as R.
  rewrite Z.add_0_r in R. exact R.
Qed.
