(* Arm c2 (op_mark), piece DECIDE (0x1407c - 0x140d0, 0x13da0): the facts the walk of LC2Dec.v uses.
   1. the placement lenv_ok gives, as linear facts;
   2. carrying the cut's memory facts over a callee's writes: a callee of this piece writes only the stack
      below the frame ([S - 65536, S - 480)) and the model block (c2d_rg), and every fact of the cut reads
      outside that region (the image's tables and strings, g_nl, g_names, long_alias, the frame, the
      payload, the marks block);
   3. the pure facts: memcmp_model, the served alias, the range of model_write's code, the model's
      answer mmark in the three outcomes of the verdict. *)
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require snprintf_c snprintf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The placement
   ========================================================================== *)

Lemma c2d_le_facts : forall E, lenv_ok E ->
  0x960e0 + 65536 <= e_S E /\ e_S E <= 2 ^ 47 /\
  4096 <= e_md E /\ e_md E + 8856 <= e_S E - 65536 /\ (e_md E + 8856 <= 0x10000 \/ 0x960e0 <= e_md E) /\
  4096 <= e_mk E /\ e_mk E + 516 <= e_S E - 65536 /\
  (e_md E + 8856 <= e_mk E \/ e_mk E + 516 <= e_md E) /\
  4096 <= e_p0 E /\ e_p0 E + Z.of_nat (length (e_pl E)) <= e_S E - 65536 /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_md E \/ e_md E + 8856 <= e_p0 E).
Proof.
  intros E LE.
  destruct LE as (S1 & S2 & S3 & (M1 & M2 & M3) & (K1 & K2 & K3) & A1 & A2 & AMK & L1 & (P1 & P2 & P3) &
                  APM & APK & LS).
  assert (IM : e_md E + MD_SIZE <= 0x10000 \/ snprintf.IMG_PAGES <= e_md E)
    by (apply snprintf.img_free_bound; [lia | unfold MD_SIZE; lia | exact M3]).
  pose proof snprintf.c_pages as CP. unfold snprintf_c.IMG_END in CP.
  unfold SLOT_STACK_Z, MD_SIZE, MK_SIZE in *. lia.
Qed.

Ltac c2d_lia LE :=
  let LF := fresh "LF" in pose proof (c2d_le_facts _ LE) as LF;
  unfold SLOT_FRAME, SLOT_STACK_Z, MD_SIZE, MK_SIZE, FO_B40, FO_B256 in *; lia.

(* closed Z.of_nat terms to their numerals *)
Ltac c2d_zn :=
  repeat match goal with |- context [Z.of_nat ?n] =>
    let v := eval vm_compute in (Z.of_nat n) in is_Zlit v; change (Z.of_nat n) with v end.

(* ==========================================================================
   2. The region a callee of this piece writes, and carrying facts across it
   ========================================================================== *)

Definition c2d_rg (E : lenv) (x : Z) : Prop :=
  (e_S E - SLOT_STACK_Z <= x < e_S E - SLOT_FRAME) \/ (e_md E <= x < e_md E + MD_SIZE).

(* every address a footprint W names is in the region *)
Definition c2d_avoid (E : lenv) (W : list ivl) : Prop :=
  forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> c2d_rg E x.

(* [a, a + n) misses the region *)
Definition c2d_off (E : lenv) (a n : Z) : Prop := forall x, a <= x < a + n -> ~ c2d_rg E x.

(* the footprint a segment of the piece reports in seg_fp *)
Definition c2d_W (E : lenv) : list ivl :=
  [(e_S E - SLOT_STACK_Z, e_S E - SLOT_FRAME); (e_md E, e_md E + MD_SIZE)].

Lemma c2d_not_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x H. cbn [outside] in H.
  destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi);
    first [ lia | exfalso; apply H; split; [lia | exact I] ].
Qed.

Lemma c2d_not_out2 : forall lo1 hi1 lo2 hi2 x, ~ outside [(lo1, hi1); (lo2, hi2)] x ->
  (lo1 <= x < hi1) \/ (lo2 <= x < hi2).
Proof.
  intros lo1 hi1 lo2 hi2 x H. cbn [outside] in H.
  destruct (Z_le_gt_dec lo1 x); destruct (Z_lt_ge_dec x hi1);
  destruct (Z_le_gt_dec lo2 x); destruct (Z_lt_ge_dec x hi2);
    first [ lia | exfalso; apply H; split; [lia | split; [lia | exact I]] ].
Qed.

Lemma c2d_off_img : forall E a n, lenv_ok E -> 0x10000 <= a -> a + n <= 0x960e0 -> c2d_off E a n.
Proof. intros E a n LE Ha Hn x Hx R. unfold c2d_rg in R. c2d_lia LE. Qed.

Lemma c2d_off_frame : forall E a n, lenv_ok E -> e_S E - SLOT_FRAME <= a -> c2d_off E a n.
Proof. intros E a n LE Ha x Hx R. unfold c2d_rg in R. c2d_lia LE. Qed.

Lemma c2d_off_low : forall E a n, lenv_ok E -> a + n <= e_S E - SLOT_STACK_Z ->
  (a + n <= e_md E \/ e_md E + MD_SIZE <= a) -> c2d_off E a n.
Proof. intros E a n LE Ha Hm x Hx R. unfold c2d_rg in R. c2d_lia LE. Qed.

Lemma c2d_munch_W : forall E W m m', c2d_avoid E W -> munch W m m' -> munch (c2d_W E) m m'.
Proof.
  intros E W m m' AV MU x Hx. apply MU.
  destruct (c2_outside_dec W (bv_unsigned x)) as [O|O]; [exact O|]. exfalso.
  pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  pose proof (AV _ R O) as RG. unfold c2d_W in Hx. cbn [outside] in Hx. unfold c2d_rg in RG. tauto.
Qed.

Lemma c2d_seg_fp : forall E m0 m, munch (c2d_W E) m0 m -> wmono rsegs m0 m -> seg_fp (e_S E) (c2_hp E) m0 m.
Proof.
  intros E m0 m MU WM. exists (c2d_W E). split; [exact MU|]. split; [exact WM|].
  intros x Hx Hn. apply c2d_not_out2 in Hn. unfold own_w.
  destruct Hn as [H|H].
  - left. unfold SLOT_FRAME in H. lia.
  - right; right; right; right; right. exists (e_md E), MD_SIZE. split; [left; reflexivity | exact H].
Qed.

(* a callee's move from m to m', writing only inside the region *)
Definition c2d_mv (E : lenv) (W : list ivl) (m m' : word -> option byte) : Prop :=
  lenv_ok E /\ munch W m m' /\ wmono rsegs m m' /\ c2d_avoid E W.

(* the interface table's names: the pointers ifptrs_at fixes, all in the image *)
Lemma c2d_link_ptrs_bound : forall i, (i < 64)%nat ->
  0x10000 <= nth i link_ptrs 0 /\ nth i link_ptrs 0 + 16 <= 0x960e0.
Proof.
  intros i Hi.
  assert (B : forallb (fun i => (0x10000 <=? nth i link_ptrs 0) && (nth i link_ptrs 0 + 16 <=? 0x960e0))
                      (seq 0 64) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B i ltac:(apply in_seq; lia)).
  apply andb_true_iff in B. destruct B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

Lemma c2d_link_names : forall i nm ix, nth_error link_tab i = Some (nm, ix) -> (length nm <= 11)%nat /\ (i < 64)%nat.
Proof.
  intros i nm ix H. split.
  - assert (B : forallb (fun e => Nat.leb (length (fst e)) 11) link_tab = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in B. specialize (B _ (nth_error_In _ _ H)). cbn [fst] in B. apply Nat.leb_le in B. exact B.
  - assert (L : length link_tab = 64%nat) by (vm_compute; reflexivity). rewrite <- L.
    apply nth_error_Some. rewrite H. discriminate.
Qed.

Lemma c2d_u64_mod : forall m a p q, u64_at m a p -> u64_at m a q -> p mod 2 ^ 64 = q mod 2 ^ 64.
Proof.
  intros m a p q (_ & _ & Hp) (_ & _ & Hq).
  assert (E : le8 (wz p) = le8 (wz q)).
  { apply nth_error_ext. intros n. destruct (Nat.lt_ge_cases n 8) as [Hn|Hn].
    - rewrite <- (Hp n) by (rewrite length_le8; exact Hn). rewrite <- (Hq n) by (rewrite length_le8; exact Hn).
      reflexivity.
    - rewrite (proj2 (nth_error_None (le8 (wz p)) n)) by (rewrite length_le8; lia).
      rewrite (proj2 (nth_error_None (le8 (wz q)) n)) by (rewrite length_le8; lia). reflexivity. }
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  apply (f_equal bv_unsigned) in E. unfold wz in E. rewrite !unsigned_lit_wrap in E. exact E.
Qed.

Section Tr.
Variables (E : lenv) (W : list ivl) (m m' : word -> option byte).
Hypothesis MV : c2d_mv E W m m'.

Lemma c2d_bytes_tr : forall a bs, c2d_off E a (Z.of_nat (length bs)) -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  pose proof MV as (LE & MU & WM & AV).
  intros a bs OF (Ha & Hl & H). split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd.
  assert (Hx : bv_unsigned (wa (a + Z.of_nat i)) = a + Z.of_nat i) by (apply wa_unsigned; lia).
  destruct (c2_outside_dec W (a + Z.of_nat i)) as [O|O].
  - rewrite (MU (wa (a + Z.of_nat i))); [reflexivity|]. rewrite Hx. exact O.
  - exfalso. apply (OF (a + Z.of_nat i)); [lia|]. apply AV; [lia | exact O].
Qed.

Lemma c2d_wr_tr : forall a n, wr_at rsegs m a n -> wr_at rsegs m' a n.
Proof. pose proof MV as (LE & MU & WM & AV). intros a n H. exact (wr_at_transport rsegs m m' a n H WM). Qed.

Lemma c2d_rwc_tr : forall a cs, c2d_off E a (Z.of_nat (cells_size cs)) -> rw_cells rsegs m a cs -> rw_cells rsegs m' a cs.
Proof.
  intros a cs OF [[Hwf Hb] Hw]. split; [split; [exact Hwf|] | exact (c2d_wr_tr _ _ Hw)].
  apply c2d_bytes_tr; [|exact Hb]. rewrite cells_bytes_length by exact Hwf. exact OF.
Qed.

Lemma c2d_u8_tr : forall a bs, c2d_off E a (Z.of_nat (length bs)) -> u8arr rsegs m a bs -> u8arr rsegs m' a bs.
Proof. intros a bs OF [Hb Hw]. split; [exact (c2d_bytes_tr a bs OF Hb) | exact (c2d_wr_tr _ _ Hw)]. Qed.

Lemma c2d_cstr_tr : forall a s, c2d_off E a (Z.of_nat (length s) + 1) -> cstr_at m a s -> cstr_at m' a s.
Proof.
  intros a s OF [Hb Hn]. split; [|exact Hn]. apply c2d_bytes_tr; [|exact Hb].
  rewrite length_app. cbn [length]. intros x Hx. apply OF. lia.
Qed.

Lemma c2d_img_tr : forall a bs, 0x10000 <= a -> a + Z.of_nat (length bs) <= 0x960e0 ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof. pose proof MV as (LE & MU & WM & AV). intros a bs H1 H2. apply c2d_bytes_tr. apply c2d_off_img; assumption. Qed.

Lemma c2d_u64_img : forall a v, 0x10000 <= a -> a + 8 <= 0x960e0 -> u64_at m a v -> u64_at m' a v.
Proof. intros a v H1 H2. unfold u64_at. apply c2d_img_tr; [exact H1|]. rewrite length_le8. lia. Qed.

Lemma c2d_u32_img : forall a v, 0x10000 <= a -> a + 4 <= 0x960e0 -> u32_at m a v -> u32_at m' a v.
Proof. intros a v H1 H2. unfold u32_at. apply c2d_img_tr; [exact H1|]. rewrite length_le4. lia. Qed.

Lemma c2d_cstr_img : forall a s, 0x10000 <= a -> a + Z.of_nat (length s) + 1 <= 0x960e0 ->
  cstr_at m a s -> cstr_at m' a s.
Proof.
  pose proof MV as (LE & MU & WM & AV).
  intros a s H1 H2. apply c2d_cstr_tr. apply c2d_off_img; [exact LE | exact H1 | lia].
Qed.

Lemma c2d_gnames_tr : gnames_at m -> gnames_at m'.
Proof.
  intros G k Hk. destruct (G k Hk) as (rest & B & L). exists rest. split; [|exact L].
  apply c2d_img_tr; [unfold A_G_NAMES; lia | rewrite L; unfold A_G_NAMES; lia | exact B].
Qed.

Lemma c2d_odd_bound : forall i, (i < 6)%nat ->
  0x10000 <= nth i odd_ptrs 0 /\ nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= 0x960e0.
Proof.
  intros i Hi.
  assert (B : forallb (fun i => (0x10000 <=? nth i odd_ptrs 0) &&
                                (nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <=? 0x960e0))
                      (seq 0 6) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B i ltac:(apply in_seq; lia)).
  apply andb_true_iff in B. destruct B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

Lemma c2d_odd_tr : odd_at m -> odd_at m'.
Proof.
  intros O i Hi. destruct (O i Hi) as [U C]. destruct (c2d_odd_bound i Hi) as [B1 B2]. split.
  - apply c2d_u64_img; [unfold A_ODD; lia | unfold A_ODD; lia | exact U].
  - apply c2d_cstr_img; [exact B1 | exact B2 | exact C].
Qed.

Lemma c2d_policy_tr : policy_ro m -> policy_ro m'.
Proof.
  intros (P1 & P2 & P3 & P4).
  split; [|split; [|split]]; (apply c2d_cstr_img; [unfold A_PREFIX, A_SERVED, A_VLAN, A_EMPTY; lia | | assumption]);
    c2d_zn; unfold A_PREFIX, A_SERVED, A_VLAN, A_EMPTY; lia.
Qed.

Lemma c2d_la_tr : la_ok m -> la_ok m'.
Proof.
  pose proof MV as (LE & MU & WM & AV).
  intros (la & sl & R & B & L). exists la, sl. split; [|split; [|exact L]].
  - apply c2d_rwc_tr; [|exact R]. apply c2d_off_img; [exact LE | unfold A_LONG_ALIAS; lia |].
    c2d_zn. unfold A_LONG_ALIAS. lia.
  - apply c2d_img_tr; [unfold A_LONG_ALIAS, LONG_ALIAS_SIZE; lia | | exact B].
    rewrite L. unfold A_LONG_ALIAS, LONG_ALIAS_SIZE. lia.
Qed.

Lemma c2d_texts_tr : texts_at m -> texts_at m'.
Proof. intros T i Hi. apply c2d_u64_img; [unfold A_TEXTS; lia | unfold A_TEXTS; lia | exact (T i Hi)]. Qed.

Lemma c2d_ifptrs_tr : ifptrs_at m -> ifptrs_at m'.
Proof.
  intros T i Hi. apply c2d_u64_img; [unfold A_G_NL, NK_IF_NAME; lia | unfold A_G_NL, NK_IF_NAME; lia | exact (T i Hi)].
Qed.

Lemma c2d_guard_tr : guard_m m -> guard_m m'.
Proof.
  intros [G1 (c & G2)]. split; [|exists c].
  - apply c2d_img_tr; [unfold A_GOT_GUARD_S; lia | rewrite length_le8; unfold A_GOT_GUARD_S; lia | exact G1].
  - apply c2d_img_tr; [unfold A_GUARD_S; lia | rewrite length_le8; unfold A_GUARD_S; lia | exact G2].
Qed.

Lemma c2d_frame_tr : forall P N j0 j1 j2, c2_frame E P N j0 j1 j2 m -> c2_frame E P N j0 j1 j2 m'.
Proof.
  pose proof MV as (LE & MU & WM & AV).
  intros P N j0 j1 j2 H. apply c2d_rwc_tr; [|exact H]. apply c2d_off_frame; [exact LE | lia].
Qed.

Lemma c2d_saved_tr : bytes_at rsegs m (e_S E - 104) (e_saved E) -> bytes_at rsegs m' (e_S E - 104) (e_saved E).
Proof.
  pose proof MV as (LE & MU & WM & AV).
  intros H. apply c2d_bytes_tr; [|exact H]. apply c2d_off_frame; [exact LE | unfold SLOT_FRAME; lia].
Qed.

Lemma c2d_cursor_tr : forall P N, cursor_ok m (e_p0 E) (e_pl E) P N -> cursor_ok m' (e_p0 E) (e_pl E) P N.
Proof.
  pose proof MV as (LE & MU & WM & AV).
  intros P N [B K]. split; [|exact K]. apply c2d_bytes_tr; [|exact B].
  apply c2d_off_low; [exact LE | c2d_lia LE | c2d_lia LE].
Qed.

Lemma c2d_name_tr : forall s, c2_name_ok m s -> c2_name_ok m' s.
Proof.
  intros s [SA SB]. split.
  - destruct (sel_name s) as [t|] eqn:Es; try rewrite Es in SA; [|exact SA].
    destruct SA as [Hnz C]. split; [exact Hnz|].
    destruct (SB t ltac:(first [exact Es | reflexivity])) as (Lt & Pl & _).
    apply c2d_cstr_img; [| | exact C];
      destruct Pl as [(P1 & P2) | (k & Hk & Ek & Lk)]; unfold A_RO_LO, A_RO_END, A_G_NAMES in *; lia.
  - intros t Ht. destruct (SB t Ht) as (Lt & Pl & (slack & Bs & Ls)). split; [exact Lt|]. split; [exact Pl|].
    exists slack. split; [|exact Ls].
    pose proof (Z.mod_pos_bound (- (sel_ptr s + Z.of_nat (length t) + 1)) 8 ltac:(lia)) as MB.
    apply c2d_img_tr; [| | exact Bs];
      destruct Pl as [(P1 & P2) | (k & Hk & Ek & Lk)]; unfold A_RO_LO, A_RO_END, A_G_NAMES in *; lia.
Qed.

Lemma c2d_marks_tr : forall gbs, c2_marks E gbs m -> c2_marks E gbs m'.
Proof.
  pose proof MV as (LE & MU & WM & AV).
  intros gbs [[U L] F]. split; [|exact F]. split; [|exact L]. apply c2d_u8_tr; [|exact U].
  rewrite L. apply c2d_off_low; [exact LE | c2d_lia LE | c2d_lia LE].
Qed.

Lemma c2d_task_tr : MemNorm.task_mem rsegs m -> MemNorm.task_mem rsegs m'.
Proof.
  pose proof MV as (LE & MU & WM & AV).
  intros TM a b H. destruct (c2_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in H. exact (TM a b H).
  - right. pose proof (bv_unsigned_in_range 64 a) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof (AV _ R O) as RG. assert (T : TASK_SIZE = 2 ^ 47) by reflexivity. rewrite T.
    unfold c2d_rg in RG. c2d_lia LE.
Qed.

Lemma c2d_kern_tr : forall i kbs, ifptrs_at m -> c2_kern i kbs m -> c2_kern i kbs m'.
Proof.
  pose proof MV as (LE & MU & WM & AV).
  intros i kbs IP (NL & WF & TB & R).
  split; [|split; [exact WF | split; [|exact R]]].
  - destruct NL as [U L]. split; [|exact L]. apply c2d_u8_tr; [|exact U].
    apply c2d_off_img; [exact LE | unfold A_G_NL; lia | rewrite L; unfold A_G_NL, NK_SIZE; lia].
  - destruct TB as (T1 & T2 & T3). split; [exact T1|]. split; [exact T2|].
    intros j nm ix Hj. destruct (T3 j nm ix Hj) as (Hix & p & Up & Pnz & Cp & Ui). split; [exact Hix|].
    destruct (c2d_link_names j nm ix Hj) as [Ln Lj].
    destruct (c2d_link_ptrs_bound j Lj) as [B1 B2].
    assert (Ep : p = nth j link_ptrs 0).
    { pose proof (c2d_u64_mod m _ p _ Up (IP j Lj)) as Mo.
      destruct Cp as [(H0 & H1 & _) _]. rewrite length_app in H1. cbn [length] in H1.
      rewrite !Z.mod_small in Mo by lia. exact Mo. }
    exists p. split; [|split; [exact Pnz | split]].
    + apply c2d_u64_img; [unfold A_G_NL, NK_IF_NAME; lia | unfold A_G_NL, NK_IF_NAME; lia | exact Up].
    + apply c2d_cstr_img; [lia | lia | exact Cp].
    + apply c2d_u32_img; [unfold A_G_NL, NK_IF_INDEX; lia | unfold A_G_NL, NK_IF_INDEX; lia | exact Ui].
Qed.

(* the cut's facts as one bundle *)
Definition c2d_rest (i s P N : Z) (j0 j1 j2 kbs gbs : list byte) (m : word -> option byte) : Prop :=
  c2_frame E P N j0 j1 j2 m /\ bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  gnames_at m /\ odd_at m /\ policy_ro m /\ la_ok m /\ texts_at m /\ ifptrs_at m /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m /\
  cursor_ok m (e_p0 E) (e_pl E) P N /\ c2_name_ok m s /\ c2_kern i kbs m /\ c2_marks E gbs m.

Lemma c2d_rest_tr : forall i s P N j0 j1 j2 kbs gbs,
  c2d_rest i s P N j0 j1 j2 kbs gbs m -> c2d_rest i s P N j0 j1 j2 kbs gbs m'.
Proof.
  pose proof MV as (LE & MU & WM & AV).
  intros i s P N j0 j1 j2 kbs gbs (FR & SV & GN & OD & PO & LA & TX & IP & ER & GU & CU & NM & KN & MK).
  split; [exact (c2d_frame_tr _ _ _ _ _ FR)|].
  split; [exact (c2d_saved_tr SV)|].
  split; [exact (c2d_gnames_tr GN)|].
  split; [exact (c2d_odd_tr OD)|].
  split; [exact (c2d_policy_tr PO)|].
  split; [exact (c2d_la_tr LA)|].
  split; [exact (c2d_texts_tr TX)|].
  split; [exact (c2d_ifptrs_tr IP)|].
  split; [exact (c2d_wr_tr _ _ ER)|].
  split; [exact (c2d_guard_tr GU)|].
  split; [exact (c2d_cursor_tr _ _ CU)|].
  split; [exact (c2d_name_tr _ NM)|].
  split; [exact (c2d_kern_tr i kbs IP KN)|].
  exact (c2d_marks_tr _ MK).
Qed.

End Tr.

Lemma c2d_rest_of : forall E i s P N j0 j1 j2 kbs gbs m,
  c2_frame E P N j0 j1 j2 m -> c2_fix E m -> cursor_ok m (e_p0 E) (e_pl E) P N -> c2_name_ok m s ->
  c2_kern i kbs m -> c2_marks E gbs m -> c2d_rest E i s P N j0 j1 j2 kbs gbs m.
Proof. intros. unfold c2_fix, c2d_rest in *. tauto. Qed.

Lemma c2d_fix_of : forall E i s P N j0 j1 j2 kbs gbs m,
  c2d_rest E i s P N j0 j1 j2 kbs gbs m -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) -> c2_fix E m.
Proof. intros. unfold c2_fix, c2d_rest in *. tauto. Qed.

(* the alias buffer (alias[256] at sp + 0x78) of the frame *)
Lemma c2d_cells_mid : forall m A pre c post,
  rw_cells rsegs m A (pre ++ c :: post) -> bytes_at rsegs m (A + Z.of_nat (cells_size pre)) (cbytes c).
Proof.
  intros m A pre c post [[Hwf Hb] _].
  apply cells_wf_app in Hwf. destruct Hwf as [Hw1 _].
  rewrite cells_bytes_app in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hw1.
  cbn [cells_bytes] in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

Lemma c2d_frame_j2 : forall E P N j0 j1 j2 m, c2_frame E P N j0 j1 j2 m ->
  bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) j2 /\ length j2 = 256%nat.
Proof.
  intros E P N j0 j1 j2 m H. split.
  - unfold c2_frame in H.
    change (lh_cells (e_md E) (e_mk E) P N j0 j1 j2) with
      ([CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY); C8 (wz (e_mk E)); C8 (wz A_G_NAMES);
        C8 (wz A_JT); C8 (wz GNL42); C8 (wz P); C8 (wz N); CB 40 j1] ++ CB 256 j2 :: []) in H.
    apply c2d_cells_mid in H. cbn [cbytes] in H. exact H.
  - destruct H as [[Hwf _] _]. unfold lh_cells in Hwf. cbn [cells_wf cell_wf] in Hwf. tauto.
Qed.

(* bytes at one address with the same length are the same bytes *)
Lemma c2d_bytes_det : forall m a l1 l2, bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros n.
  destruct (Nat.lt_ge_cases n (length l1)) as [Hn|Hn].
  - rewrite <- (H1 n Hn). rewrite <- (H2 n) by lia. reflexivity.
  - rewrite (proj2 (nth_error_None l1 n)) by lia. rewrite (proj2 (nth_error_None l2 n)) by lia. reflexivity.
Qed.

(* a C string at a is the prefix of the bytes there *)
Lemma c2d_prefix : forall m a s big, cstr_at m a s -> bytes_at rsegs m a big -> (length s < length big)%nat ->
  firstn (S (length s)) big = s ++ [zb 0].
Proof.
  intros m a s big [Bs _] Bb L.
  pose proof (proj1 (bytes_at_app rsegs m a (firstn (S (length s)) big) (skipn (S (length s)) big))) as H.
  rewrite firstn_skipn in H. destruct (H Bb) as [B1 _].
  apply (c2d_bytes_det m a); [exact B1 | exact Bs |]. rewrite length_firstn, length_app. cbn [length]. lia.
Qed.

Lemma c2d_firstn_bytes : forall m a big k, bytes_at rsegs m a big -> bytes_at rsegs m a (firstn k big).
Proof.
  intros m a big k Bb.
  pose proof (proj1 (bytes_at_app rsegs m a (firstn k big) (skipn k big))) as H.
  rewrite firstn_skipn in H. exact (proj1 (H Bb)).
Qed.

(* ==========================================================================
   3. Pure facts
   ========================================================================== *)

Lemma c2d_memcmp : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  exists v, memcmp_model l r n = Some v /\ -256 < v < 256 /\ (v = 0 <-> firstn n l = firstn n r).
Proof.
  induction n as [|n IH]; intros l r Hl Hr.
  - exists 0. split; [reflexivity|]. split; [lia|]. split; intros _; reflexivity.
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn [length] in Hl, Hr. cbn [memcmp_model firstn].
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    change (bv_modulus 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Eab|Eab].
    + destruct (IH l r ltac:(lia) ltac:(lia)) as (v & Hv & Rv & Iv). exists v. split; [exact Hv|]. split; [exact Rv|].
      assert (Ab : a = b) by (apply bv_eq; exact Eab). subst b.
      split.
      * intros H0. apply Iv in H0. rewrite H0. reflexivity.
      * intros H0. apply Iv. exact (f_equal (@tl byte) H0).
    + exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
      split; [intros H0; exfalso; lia|].
      intros H0. exfalso. apply (f_equal (@hd byte a)) in H0. cbn [hd] in H0. apply Eab. rewrite H0. reflexivity.
Qed.

Lemma c2d_nonul : forall l, existsb (fun b => bz b =? 0) l = false -> ~ In (zb 0) l.
Proof.
  intros l H Hin.
  assert (T : existsb (fun b => bz b =? 0) l = true)
    by (apply existsb_exists; exists (zb 0); split; [exact Hin | reflexivity]).
  congruence.
Qed.

Lemma c2d_nonul_served : ~ In (zb 0) S_SERVED.
Proof. apply c2d_nonul. vm_compute. reflexivity. Qed.

Lemma c2d_in_firstn : forall (x : byte) k l, In x (firstn k l) -> In x l.
Proof. intros x k l H. rewrite <- (firstn_skipn k l). apply in_or_app. left. exact H. Qed.

(* the first 15 bytes of the alias buffer are "reac-pw:served\0" exactly when the alias is "reac-pw:served" *)
Lemma c2d_served : forall al j2, ~ In (zb 0) al -> firstn (S (length al)) j2 = al ++ [zb 0] ->
  (15 <= length j2)%nat -> (firstn 15 j2 = S_SERVED ++ [zb 0] <-> al = S_SERVED).
Proof.
  intros al j2 Hn Hp Hl. split.
  - intros Hf.
    destruct (Nat.lt_trichotomy (length al) 14) as [Lt|[Eq|Gt]].
    + exfalso.
      assert (H1 : firstn (S (length al)) (S_SERVED ++ [zb 0]) = al ++ [zb 0]).
      { rewrite <- Hf, firstn_firstn. rewrite (Nat.min_l (S (length al)) 15) by lia. exact Hp. }
      rewrite firstn_app in H1.
      replace (S (length al) - length S_SERVED)%nat with 0%nat in H1 by (change (length S_SERVED) with 14%nat; lia).
      cbn [firstn] in H1. rewrite app_nil_r in H1.
      apply c2d_nonul_served. apply (c2d_in_firstn _ (S (length al))). rewrite H1.
      apply in_or_app. right. left. reflexivity.
    + rewrite Eq in Hp. rewrite Hp in Hf. apply app_inj_tail in Hf. exact (proj1 Hf).
    + exfalso.
      assert (H1 : firstn 15 (al ++ [zb 0]) = S_SERVED ++ [zb 0]).
      { rewrite <- Hp, firstn_firstn. rewrite (Nat.min_l 15 (S (length al))) by lia. exact Hf. }
      rewrite firstn_app in H1. replace (15 - length al)%nat with 0%nat in H1 by lia.
      cbn [firstn] in H1. rewrite app_nil_r in H1.
      apply Hn. apply (c2d_in_firstn _ 15). rewrite H1. apply in_or_app. right. left. reflexivity.
  - intros ->. exact Hp.
Qed.

(* the code model_write answers is an int: at least -2^31, at most RC_FAILS *)
Lemma c2d_rd32s_lb : forall c off, - 2 ^ 31 <= rd32s c off.
Proof.
  intros c off. unfold rd32s, rd32, rdn. cbv zeta.
  pose proof (bytes_le_to_Z_nonneg (slice c off 4)) as H.
  destruct (Z.ltb_spec (bytes_le_to_Z (slice c off 4)) (2 ^ 31)); cbv beta iota; lia.
Qed.

Lemma c2d_msg_lb : forall fuel c off left code, msg_scan fuel c off left = NlErr code -> - 2 ^ 31 <= code.
Proof.
  induction fuel as [|f IH]; intros c off left code H; cbn [msg_scan] in H; [discriminate|].
  revert H.
  repeat (match goal with |- (if ?b then _ else _) = _ -> _ => destruct b; cbv beta iota end);
  intros H;
  first [ discriminate H
        | injection H as <-; apply c2d_rd32s_lb
        | exact (IH _ _ _ _ H) ].
Qed.

Lemma c2d_loop_lb : forall fuel cs i code j, chunk_loop fuel cs i = (NlErr code, j) -> - 2 ^ 31 <= code.
Proof.
  induction fuel as [|f IH]; intros cs i code j H; cbn [chunk_loop] in H; [discriminate|].
  revert H. destruct (nth_error cs i) as [c|]; intros H; [|discriminate H].
  revert H. destruct (chunk_walk c) as [| | c0 | a] eqn:Ew; intros H; try discriminate H.
  - exact (IH _ _ _ _ H).
  - injection H as Hc Hj. subst c0. unfold chunk_walk in Ew. exact (c2d_msg_lb _ _ _ _ _ Ew).
Qed.

Lemma c2d_talk_lb : forall K, 0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 31 <= talk_rc_lib K.
Proof.
  intros K H1 H2 H3. unfold talk_rc_lib, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn; lia|].
  destruct (negb (k_send K =? 0)); [cbn; lia|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j] eqn:Ec.
  destruct v as [| | code | a]; cbn; [lia | try unfold E_IO; lia | exact (c2d_loop_lb _ _ _ _ _ Ec) | lia].
Qed.

Lemma c2d_wrc_range : forall tab nm al reqs K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 31 <= w_rc (write_model tab nm al reqs K) <= RC_FAILS.
Proof.
  intros tab nm al reqs K H1 H2 H3. unfold write_model. cbn [w_rc]. unfold norm_rc.
  assert (L : - 2 ^ 31 <= w_rc (write_core tab nm al reqs K)).
  { unfold write_core. destruct nm as [s|]; [|cbn; try unfold E_INVAL; lia].
    destruct al as [a|]; [|cbn; try unfold E_INVAL; lia]. cbv zeta.
    repeat (match goal with |- context [if ?b then _ else _] => destruct b; cbv beta iota end); cbn [w_rc];
      first [ try unfold E_INVAL; lia | try unfold E_NAMETOOLONG; lia | try unfold E_NODEV; lia
            | exact (c2d_talk_lb K H1 H2 H3) ]. }
  destruct (Z.ltb_spec 0 (w_rc (write_core tab nm al reqs K))); cbv beta iota; unfold RC_FAILS; lia.
Qed.

Lemma c2d_wz_zero : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_unsigned (wz z) = 0 -> z = 0.
Proof.
  intros z Hz H. unfold wz in H. rewrite unsigned_lit_wrap in H.
  destruct (Z.ltb_spec z 0).
  - rewrite <- (Z.mod_add z 1 (2 ^ 64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
  - rewrite Z.mod_small in H by lia. exact H.
Qed.

(* the model's answer, once the read has answered 0 for a non-empty name *)
Lemma c2d_MM_eq : forall s kbs gbs t, sel_name s = Some t -> t <> [] -> r_rc (c2_rd t kbs) = 0 ->
  c2_MM s kbs gbs =
    (if decide (Some (r_kind (c2_rd t kbs))) (Some (r_alias (c2_rd t kbs))) =? V_MARK
     then (if negb (w_rc (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))) =? 0)
           then Mres (w_rc (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))))
                     (mk_names gbs)
                     (w_reqs (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))))
                     (w_state (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))))
           else Mres (decide (Some (r_kind (c2_rd t kbs))) (Some (r_alias (c2_rd t kbs))))
                     (remember (mk_names gbs) t)
                     (w_reqs (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))))
                     (w_state (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs)))))
     else if (decide (Some (r_kind (c2_rd t kbs))) (Some (r_alias (c2_rd t kbs))) =? V_OURS)
             && bl_eqb (r_alias (c2_rd t kbs)) S_SERVED
     then Mres (decide (Some (r_kind (c2_rd t kbs))) (Some (r_alias (c2_rd t kbs))))
               (remember (mk_names gbs) t) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))
     else Mres (decide (Some (r_kind (c2_rd t kbs))) (Some (r_alias (c2_rd t kbs))))
               (mk_names gbs) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))).
Proof.
  intros s kbs gbs t Hs Ht Hr. unfold c2_MM, mmark. rewrite Hs.
  destruct t as [|x t']; [congruence|]. cbn [length Nat.eqb]. cbv zeta.
  unfold c2_rd in Hr |- *. rewrite Hr. reflexivity.
Qed.

Lemma c2d_MM_leave : forall s kbs gbs t v, sel_name s = Some t -> t <> [] -> r_rc (c2_rd t kbs) = 0 ->
  decide (Some (r_kind (c2_rd t kbs))) (Some (r_alias (c2_rd t kbs))) = v -> v <> V_MARK ->
  (v <> V_OURS \/ bl_eqb (r_alias (c2_rd t kbs)) S_SERVED = false) ->
  c2_MM s kbs gbs = Mres v (mk_names gbs) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs)).
Proof.
  intros s kbs gbs t v Hs Ht Hr Hv Hm Ho. rewrite (c2d_MM_eq s kbs gbs t Hs Ht Hr). rewrite Hv.
  destruct (Z.eqb_spec v V_MARK) as [E|_]; [contradiction|].
  destruct Ho as [Hn|Hb].
  - destruct (Z.eqb_spec v V_OURS) as [E|_]; [contradiction|]. reflexivity.
  - rewrite Hb, andb_false_r. reflexivity.
Qed.

Lemma c2d_MM_served : forall s kbs gbs t, sel_name s = Some t -> t <> [] -> r_rc (c2_rd t kbs) = 0 ->
  decide (Some (r_kind (c2_rd t kbs))) (Some (r_alias (c2_rd t kbs))) = V_OURS ->
  bl_eqb (r_alias (c2_rd t kbs)) S_SERVED = true ->
  c2_MM s kbs gbs = Mres V_OURS (remember (mk_names gbs) t) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs)).
Proof.
  intros s kbs gbs t Hs Ht Hr Hv Hb. rewrite (c2d_MM_eq s kbs gbs t Hs Ht Hr). rewrite Hv, Hb. reflexivity.
Qed.

Lemma c2d_MM_mark : forall s kbs gbs t, sel_name s = Some t -> t <> [] -> r_rc (c2_rd t kbs) = 0 ->
  decide (Some (r_kind (c2_rd t kbs))) (Some (r_alias (c2_rd t kbs))) = V_MARK ->
  let w := write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs)) in
  c2_MM s kbs gbs =
    if negb (w_rc w =? 0) then Mres (w_rc w) (mk_names gbs) (w_reqs w) (w_state w)
    else Mres V_MARK (remember (mk_names gbs) t) (w_reqs w) (w_state w).
Proof.
  intros s kbs gbs t Hs Ht Hr Hv. cbv zeta. rewrite (c2d_MM_eq s kbs gbs t Hs Ht Hr). rewrite Hv. reflexivity.
Qed.

(* the read's alias fits its buffer *)
Lemma c2d_alias_len : forall t kbs, (length (r_alias (c2_rd t kbs)) <= 255)%nat.
Proof.
  intros t kbs. unfold c2_rd, read_model, read_core. cbn [r_alias].
  destruct (Nat.eqb (length t) 0); [cbn; lia|]. cbv zeta.
  destruct (index_of link_tab t =? 0); cbn [r_alias]; [cbn; lia|].
  destruct (ALIAS_MAX <? 1); [cbn; lia|].
  destruct (a_alias (talk_attrs (nk_kstate kbs))) as [pay|]; cbn [text_of_attr]; [|cbn; lia].
  pose proof (cut_text_len pay ALIAS_MAX ltac:(unfold ALIAS_MAX; lia)) as L. unfold ALIAS_MAX in *. lia.
Qed.
