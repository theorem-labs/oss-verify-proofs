(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_tables.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
Definition WIN (s : mstate) : Prop :=
  alloc_ceiling <= ms_lo s /\ ms_lo s <= ms_hi s /\ ms_hi s <= 2^64.

Lemma WIN_upd : forall s m h, WIN s -> WIN (upd s m h).
Proof. intros s m h H. exact H. Qed.

Lemma acc_ok_heap : forall s a n, WIN s -> 0 <= a -> 0 <= n -> a + n <= alloc_ceiling ->
  acc_ok s (Z_to_bv 64 a) n = true.
Proof.
  intros s a n (W1 & W2 & W3) Ha Hn Hc. ceil.
  unfold acc_ok. rewrite u_lit by llia. apply Bool.orb_true_iff. left. apply Z.leb_le. llia.
Qed.

(* [comment removed for export] *)
Lemma st_zone_heap : forall a n, 0 <= a -> 0 <= n -> a + n <= alloc_ceiling ->
  (a + n <= IMG_LO \/ IMG_HI <= a) -> st_zone (Z_to_bv 64 a) n = true.
Proof.
  intros a n Ha Hn Hc Hh. ceil. apply (proj2 (st_zone_spec _ _)). rewrite u_lit by llia. llia.
Qed.

Lemma st_zone_ctx : forall a n, CTX <= a -> a + n <= CTX_END -> 0 <= n -> st_zone (Z_to_bv 64 a) n = true.
Proof.
  intros a n Ha Hb Hn. unfold CTX, CTX_END in *. apply (proj2 (st_zone_spec _ _)). rewrite u_lit by llia. llia.
Qed.

Lemma st_zone_errno : st_zone A_ERRNO 4 = true.
Proof. apply (proj2 (st_zone_spec _ _)). unfold ERRNO. lia. Qed.

Lemma dom_heap : forall A x, WF A -> dom A x -> exists lo hi, heap_range lo hi /\ lo <= x < hi.
Proof.
  intros A x HW [ (pg & Hpg & Hx) | [ (ma & mt & aib & slots & Hma & Hr & Hml & Hx) | (pg & Hpg & Hx) ] ].
  - destruct (wf_areas_al A HW pg Hpg) as [_ Hh]. exists pg, (pg + 4096). split; [exact Hh | llia].
  - destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpg).
    destruct (Hpg Hml) as [_ Hh]. exists (mt_mem mt), (mt_mem mt + grp_map_len mt). split; [exact Hh | llia].
  - destruct (wf_pages_al A HW pg Hpg) as [_ Hh]. exists pg, (pg + 4096). split; [exact Hh | llia].
Qed.

Lemma st_zone_dom : forall A a (n : nat), WF A -> (forall j, 0 <= j < Z.of_nat n -> dom A (a + j)) -> (0 < n)%nat ->
  st_zone (Z_to_bv 64 a) (Z.of_nat n) = true.
Proof.
  intros A a n HW Hd Hn.
  assert (H0 : dom A (a + 0)) by (apply Hd; llia).
  assert (H1 : dom A (a + (Z.of_nat n - 1))) by (apply Hd; llia).
  destruct (dom_heap A _ HW H0) as (lo & hi & Hr & Hlo & Hhi).
  destruct (dom_heap A _ HW H1) as (lo' & hi' & Hr' & Hlo' & Hhi').
  unfold heap_range in Hr, Hr'. ceil.
  apply st_zone_heap; [llia | llia | ceil; llia |].
  destruct (Z.le_gt_cases (a + Z.of_nat n) IMG_LO) as [Hle | Hgt]; [left; exact Hle|].
  destruct (Z.le_gt_cases IMG_HI a) as [Hle' | Hgt']; [right; exact Hle'|].
  exfalso.
  (* [comment removed for export] *)
  destruct (Z.le_gt_cases IMG_LO a) as [Ha | Ha].
  - (* [comment removed for export] *) llia.
  - assert (H2 : dom A (a + (IMG_LO - a))) by (apply Hd; llia).
    destruct (dom_heap A _ HW H2) as (lo2 & hi2 & Hr2 & Hlo2 & Hhi2). unfold heap_range in Hr2. llia.
Qed.

Section Steps.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  (* [comment removed for export] *)
  Lemma ts_ld_meta : forall s ma mt fl (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> a_meta A ma = Some mt -> mlen fl = 8 -> 0 <= mt_f mt fl < 2^64 ->
    tsafe (k (Z_to_bv 64 (mt_f mt fl)) s) P ->
    tsafe ((x <- m_ld (Z_to_bv 64 (ma + moff fl)) ;; k x) s) P.
  Proof.
    intros s ma mt fl k P HR HWn Hma Hlen Hv Hk.
    destruct (rep_read_meta A HW ma mt Hma (ms_mem s) fl HR ltac:(llia)) as (bs & Hrd & Hl & Hval).
    rewrite Hlen in *. change (Z.to_nat 8) with 8%nat in *.
    destruct (has_addr A HW (FCT (ma + moff fl) (mlen fl) (mt_f mt fl))
                ltac:(right; right; left; exists ma, mt, fl; auto)) as (H1 & H2 & H3 & _). cbn in H1, H2, H3.
    eapply ts_ld; [apply acc_ok_heap; [exact HWn | llia | llia | llia] | exact Hrd |].
    rewrite (le_val_Z bs (mt_f mt fl)); [exact Hk|]. rewrite Hval. apply Z.mod_small. change (2^(8*8)) with (2^64). llia.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_lw_meta : forall s ma mt fl (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> a_meta A ma = Some mt -> mlen fl = 4 -> 0 <= mt_f mt fl < 2^32 ->
    tsafe (k (Z_to_bv 64 (bv_swrap 32 (mt_f mt fl))) s) P ->
    tsafe ((x <- m_lw (Z_to_bv 64 (ma + moff fl)) ;; k x) s) P.
  Proof.
    intros s ma mt fl k P HR HWn Hma Hlen Hv Hk.
    destruct (rep_read_meta A HW ma mt Hma (ms_mem s) fl HR ltac:(llia)) as (bs & Hrd & Hl & Hval).
    rewrite Hlen in *. change (Z.to_nat 4) with 4%nat in *.
    destruct (has_addr A HW (FCT (ma + moff fl) (mlen fl) (mt_f mt fl))
                ltac:(right; right; left; exists ma, mt, fl; auto)) as (H1 & H2 & H3 & _). cbn in H1, H2, H3.
    eapply ts_lw; [apply acc_ok_heap; [exact HWn | llia | llia | llia] | exact Hrd |].
    rewrite (le_val_Z bs (mt_f mt fl)); [rewrite v_lw_Z by llia; exact Hk|].
    rewrite Hval. apply Z.mod_small. change (2^(8*4)) with (2^32). llia.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_ld_ctx : forall s ck (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 8 -> 0 <= a_ctx A ck < 2^64 ->
    tsafe (k (Z_to_bv 64 (a_ctx A ck)) s) P ->
    tsafe ((x <- m_ld (Z_to_bv 64 (caddr ck)) ;; k x) s) P.
  Proof.
    intros s ck k P HR HWn Hk Hlen Hv Hk'.
    destruct (rep_read_ctx A (ms_mem s) ck HR Hk ltac:(llia)) as (bs & Hrd & Hl & Hval).
    rewrite Hlen in *. change (Z.to_nat 8) with 8%nat in *.
    pose proof (ctx_slot_range ck Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    eapply ts_ld; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; llia] | exact Hrd |].
    rewrite (le_val_Z bs (a_ctx A ck)); [exact Hk'|]. rewrite Hval. apply Z.mod_small. change (2^(8*8)) with (2^64). llia.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_lw_ctx : forall s ck (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 4 -> 0 <= a_ctx A ck < 2^32 ->
    tsafe (k (Z_to_bv 64 (bv_swrap 32 (a_ctx A ck))) s) P ->
    tsafe ((x <- m_lw (Z_to_bv 64 (caddr ck)) ;; k x) s) P.
  Proof.
    intros s ck k P HR HWn Hk Hlen Hv Hk'.
    destruct (rep_read_ctx A (ms_mem s) ck HR Hk ltac:(llia)) as (bs & Hrd & Hl & Hval).
    rewrite Hlen in *. change (Z.to_nat 4) with 4%nat in *.
    pose proof (ctx_slot_range ck Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    eapply ts_lw; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; llia] | exact Hrd |].
    rewrite (le_val_Z bs (a_ctx A ck)); [rewrite v_lw_Z by llia; exact Hk'|].
    rewrite Hval. apply Z.mod_small. change (2^(8*4)) with (2^32). llia.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_lbu_ctx : forall s ck (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 1 -> 0 <= a_ctx A ck < 256 ->
    tsafe (k (Z_to_bv 64 (a_ctx A ck)) s) P ->
    tsafe ((x <- m_lbu (Z_to_bv 64 (caddr ck)) ;; k x) s) P.
  Proof.
    intros s ck k P HR HWn Hk Hlen Hv Hk'.
    destruct (rep_read_ctx A (ms_mem s) ck HR Hk ltac:(llia)) as (bs & Hrd & Hl & Hval).
    rewrite Hlen in *. change (Z.to_nat 1) with 1%nat in *.
    pose proof (ctx_slot_range ck Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    destruct bs as [|b [|]]; try (cbn in Hl; llia).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; llia] | exact Hrd |].
    rewrite bytes_le_single in Hval. rewrite Hval. rewrite Z.mod_small by (change (2^(8*1)) with 256; llia). exact Hk'.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_lhu_size_class : forall s j (k : word -> M R) P,
    rodata_clear (ms_mem s) -> WIN s -> 0 <= j < 48 ->
    tsafe (k (Z_to_bv 64 (size_class j)) s) P ->
    tsafe ((x <- m_lhu (Z_to_bv 64 (T_SIZE_CLASSES + 2 * j)) ;; k x) s) P.
  Proof.
    intros s j k P Hc HWn Hj Hk.
    destruct (read_size_class (ms_mem s) j Hc Hj) as (bs & Hrd & Hl & Hval).
    eapply ts_lhu; [apply acc_ok_heap; [exact HWn | pose proof layout_tabs; lia | lia | pose proof layout_tabs; llia] | exact Hrd |].
    rewrite (le_val_Z bs (size_class j) Hval). exact Hk.
  Qed.

  Lemma ts_lbu_debruijn : forall s j (k : word -> M R) P,
    rodata_clear (ms_mem s) -> WIN s -> 0 <= j < 32 ->
    tsafe (k (Z_to_bv 64 (debruijn j)) s) P ->
    tsafe ((x <- m_lbu (Z_to_bv 64 (T_DEBRUIJN + j)) ;; k x) s) P.
  Proof.
    intros s j k P Hc HWn Hj Hk.
    destruct (read_debruijn (ms_mem s) j Hc Hj) as (b & Hrd & Hval).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWn | pose proof layout_tabs; lia | lia | pose proof layout_tabs; llia] | exact Hrd |].
    rewrite Hval. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_lbu_dom : forall s a (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> dom A a ->
    (forall b, 0 <= b < 256 -> tsafe (k (Z_to_bv 64 b) s) P) ->
    tsafe ((x <- m_lbu (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s a k P HR HWn Hd Hk.
    pose proof (dom_addr A HW a Hd) as Ha.
    destruct (rep_read_dom A (ms_mem s) HR a 1 ltac:(intros j Hj; replace (a + j) with a by llia; exact Hd) ltac:(llia) ltac:(ceil; cbn; llia))
      as (bs & Hrd & Hl).
    destruct bs as [|b [|]]; try (cbn in Hl; llia).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWn | llia | llia | llia] | exact Hrd |].
    apply Hk. pose proof (u8_range b). llia.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_lhu_dom : forall s a (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> dom A a -> dom A (a + 1) ->
    (forall v, 0 <= v < 2^16 -> tsafe (k (Z_to_bv 64 v) s) P) ->
    tsafe ((x <- m_lhu (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s a k P HR HWn Hd0 Hd1 Hk.
    pose proof (dom_addr A HW a Hd0) as Ha. pose proof (dom_addr A HW _ Hd1) as Ha1.
    destruct (rep_read_dom A (ms_mem s) HR a 2) as (bs & Hrd & Hl);
      [ intros j Hj; destruct (Z.eq_dec j 0) as [->|]; [rewrite Z.add_0_r; exact Hd0 | replace (a + j) with (a + 1) by llia; exact Hd1]
      | llia | ceil; cbn; llia | ].
    eapply ts_lhu; [apply acc_ok_heap; [exact HWn | llia | llia | llia] | exact Hrd |].
    rewrite (le_val_Z bs (bytes_le_to_Z bs) eq_refl). apply Hk.
    pose proof (bytes_le_to_Z_bound bs) as Hb. pose proof (bytes_le_to_Z_nonneg bs). rewrite Hl in Hb. cbn in Hb. llia.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_lbu_fact : forall s a v (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> has A (FCT a 1 v) -> 0 <= v < 256 ->
    tsafe (k (Z_to_bv 64 v) s) P ->
    tsafe ((x <- m_lbu (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s a v k P HR HWn Hf Hv Hk.
    destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3.
    destruct (rep_read A (ms_mem s) HR a 1 v Hf ltac:(llia) ltac:(ceil; cbn; llia) ltac:(llia)) as (bs & Hrd & Hl & Hval).
    destruct bs as [|b [|]]; try (cbn in Hl; llia).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWn | llia | llia | cbn; llia] | exact Hrd |].
    rewrite bytes_le_single in Hval. rewrite Hval. rewrite Z.mod_small by (change (2^(8*Z.of_nat 1)) with 256; llia). exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_st_clear : forall s n a v (k : unit -> M R) P,
    Rep A (ms_mem s) -> WIN s -> (0 < n)%nat ->
    (forall j, 0 <= j < Z.of_nat n -> dom A (a + j)) ->
    (forall f, has A f -> f_a f + f_n f <= a \/ a + Z.of_nat n <= f_a f) ->
    (Rep A (wbytes (ms_mem s) (Z_to_bv 64 a) (word_to_le_bytes n v)) ->
     tsafe (k tt (upd s (wbytes (ms_mem s) (Z_to_bv 64 a) (word_to_le_bytes n v)) (ms_vm s))) P) ->
    tsafe ((x <- m_st n (Z_to_bv 64 a) v ;; k x) s) P.
  Proof.
    intros s n a v k P HR HWn Hn Hd Hclear Hk.
    pose proof (dom_addr A HW a ltac:(replace a with (a + 0) by llia; apply Hd; llia)) as Ha.
    pose proof (dom_addr A HW (a + (Z.of_nat n - 1)) ltac:(apply Hd; llia)) as Hb.
    ceil.
    eapply ts_st.
    - apply acc_ok_heap; [exact HWn | llia | llia | ceil; llia].
    - apply (st_zone_dom A); [exact HW | exact Hd | exact Hn].
    - eapply store_ok_dom; [exact HR | exact Hd | llia | llia].
    - apply Hk. apply (rep_write_clear A); [exact HR | llia | rewrite length_N_to_le_bytes; llia | rewrite length_N_to_le_bytes; exact Hclear | exact (facts_addr64 A HW)].
  Qed.
End Steps.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_31 : forall w, 0 <= w -> Z.land w 31 = w mod 32.
Proof. intros w Hw. change 31 with (2^5 - 1). rewrite land_ones_low by llia. reflexivity. Qed.

Lemma land_pagemask : forall w, 0 <= w < 2^64 -> Z.land w (2^64 - 4096) = 4096 * (w / 4096).
Proof.
  intros w Hw. change 4096 with (2^12) at 1. rewrite land_high_mask by llia.
  pose proof (Z.div_mod w 4096 ltac:(llia)). change (2^12) with 4096. llia.
Qed.

Lemma testbit_double : forall a i, 0 <= a -> 0 <= i -> Z.testbit (2 * a) i = if i =? 0 then false else Z.testbit a (i - 1).
Proof.
  intros a i Ha Hi. destruct (Z.eqb_spec i 0) as [-> | Hne].
  - rewrite Z.testbit_even_0. reflexivity.
  - replace i with (Z.succ (i - 1)) at 1 by llia. rewrite Z.testbit_even_succ by llia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sc_index : forall w, 0 <= w -> Z.land (w / 32) 126 = 2 * ((w / 64) mod 64).
Proof.
  intros w Hw.
  change 32 with (2^5). change 64 with (2^6). change 126 with (2 * Z.ones 6).
  assert (H1 : 0 <= w / 2^5) by (apply Z.div_pos; llia).
  assert (H2 : 0 <= w / 2^6) by (apply Z.div_pos; llia).
  assert (H3 : 0 <= (w / 2^6) mod 2^6) by (apply Z.mod_pos_bound; llia).
  apply Z.bits_inj'. intros i Hi.
  assert (HO : 0 <= Z.ones 6) by (change (Z.ones 6) with 63; llia).
  rewrite Z.land_spec. rewrite (testbit_double (Z.ones 6)) by llia. rewrite (testbit_double ((w / 2^6) mod 2^6)) by llia.
  destruct (Z.eqb_spec i 0) as [-> | Hne]; [apply andb_false_r|].
  rewrite Z.testbit_ones by llia.
  destruct (Z.lt_ge_cases (i - 1) 6) as [Hl | Hl].
  - rewrite Z.mod_pow2_bits_low by llia. rewrite !Z.div_pow2_bits by llia.
    replace (i - 1 + 6) with (i + 5) by llia.
    replace ((0 <=? i - 1) && (i - 1 <? 6))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; llia).
    rewrite andb_true_r. reflexivity.
  - rewrite Z.mod_pow2_bits_high by llia.
    replace ((0 <=? i - 1) && (i - 1 <? 6))%bool with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; llia).
    apply andb_false_r.
Qed.

Section Stride.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.

  (* [comment removed for export] *)
  Lemma ts_class_stride : forall s W (kk : word -> M R) P,
    rodata_clear (ms_mem s) -> WIN s -> 0 <= W < 2^64 -> (W / 64) mod 64 < 48 ->
    tsafe (kk (Z_to_bv 64 (16 * size_class ((W / 64) mod 64))) s) P ->
    tsafe ((szc <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli (Z_to_bv 64 W) 5) 126)) ;; kk (v_slli szc 4)) s) P.
  Proof.
    intros s W kk P HRO HWn HW64 Hsc Hk.
    assert (H5 : 0 <= W / 2^5 < 2^64) by (split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia]).
    pose proof (Z.mod_pos_bound (W / 64) 64 ltac:(llia)) as Hm.
    rewrite v_srli_Z by llia. rewrite v_andi_Z by llia. change (2^5) with 32. rewrite sc_index by llia.
    rewrite A_SIZE_CLASSES_eq, v_add_Z.
    eapply ts_lhu_size_class; [exact HRO | exact HWn | llia |].
    pose proof (size_class_bound ((W / 64) mod 64) ltac:(llia)).
    rewrite v_slli_Z by llia. change (2^4) with 16. rewrite Z.mul_comm. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_get_stride : forall s ma mt aib slots (kk : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> rodata_clear (ms_mem s) ->
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
    tsafe (kk (Z_to_bv 64 (mt_stride mt)) s) P ->
    tsafe ((x <- (if negb (is0 (v_srli (Z_to_bv 64 (mt_w32 mt)) 12)) && is0 (v_andi (Z_to_bv 64 (mt_w32 mt)) 31)
                  then mret (v_addi (v_and (Z_to_bv 64 (mt_w32 mt)) PAGEMASK) (-16))
                  else szc <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli (Z_to_bv 64 (mt_w32 mt)) 5) 126)) ;;
                       mret (v_slli szc 4)) ;; kk x) s) P.
  Proof.
    intros s ma mt aib slots kk P HR HWn HRO Hma Hr Hk.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    set (W := mt_w32 mt) in *.
    assert (Hml : mt_maplen mt = W / 4096) by reflexivity.
    assert (Hlast : mt_last mt = W mod 32) by reflexivity.
    assert (Hscw : mt_sc mt = (W / 64) mod 64) by reflexivity.
    pose proof (Z.div_pos W 4096 ltac:(llia) ltac:(llia)) as Hml0.
    assert (HmlB : W / 4096 < 2^52) by (apply Z.div_lt_upper_bound; llia).
    pose proof (Z.mod_pos_bound W 32 ltac:(llia)) as Hl0.
    rewrite v_srli_Z by llia. rewrite is0_Z by (change (2^12) with 4096; llia).
    rewrite v_andi_Z by llia. rewrite land_31 by llia. rewrite is0_Z by llia.
    change (2^12) with 4096.
    assert (FIN : forall v s', v = mt_stride mt -> tsafe (kk (Z_to_bv 64 (mt_stride mt)) s') P -> tsafe (kk (Z_to_bv 64 v) s') P)
      by (intros v s' -> H; exact H).
    assert (CLS : (W / 4096 =? 0) || negb (W mod 32 =? 0) = true ->
                  tsafe ((x <- (szc <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli (Z_to_bv 64 W) 5) 126)) ;;
                                mret (v_slli szc 4)) ;; kk x) s) P).
    { intros Hb. reassoc.
      assert (Hsc48 : mt_sc mt < 48).
      { destruct Hsc as [?|(? & Hl & Hm)]; [llia|]. exfalso. rewrite Hml, Hlast in *.
        apply Bool.orb_true_iff in Hb. destruct Hb as [Hb|Hb]; [apply Z.eqb_eq in Hb; llia | apply Bool.negb_true_iff in Hb; apply Z.eqb_neq in Hb; llia]. }
      pose proof (w_sc_range W) as Hscr. unfold w_sc in Hscr.
      apply (ts_class_stride s W); [exact HRO | exact HWn | llia | rewrite <- Hscw; exact Hsc48 |].
      apply FIN; [| exact Hk]. unfold mt_stride. rewrite Hml, Hlast, Hb, Hscw. reflexivity. }
    destruct (W / 4096 =? 0) eqn:E1; destruct (W mod 32 =? 0) eqn:E2; cbn [negb andb];
      try (apply CLS; reflexivity).
    (* [comment removed for export] *)
    unfold mbind at 1, mret. cbn [tbind].
    rewrite PAGEMASK_eq, v_and_Z by llia. rewrite land_pagemask by llia. rewrite v_addi_Z.
    apply FIN; [| exact Hk]. unfold mt_stride. rewrite Hml, Hlast, E1, E2. cbn [negb orb]. llia.
  Qed.
End Stride.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma grp_dom : forall A ma mt aib slots x, WF A ->
  a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
  gext_lo mt <= x < gext_hi mt + 4 -> dom A x.
Proof.
  intros A ma mt aib slots x HW Hma Hr Hx.
  destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi & _).
  right; left. exists mr, mtr, aibr, slr. repeat split; auto; llia.
Qed.

(* [comment removed for export] *)
Lemma ts_bind_split : forall {R B : Type} (c : M B) (K : B -> M R) s P (Q : B -> mstate -> Prop),
  tsafe (c s) Q -> (forall o s', Q o s' -> tsafe (K o s') P) -> tsafe (mbind c K s) P.
Proof.
  intros R B c K s P Q Hc HK. unfold mbind. eapply tsafe_bind; [exact Hc | exact HK].
Qed.

(* [comment removed for export] *)
Lemma iS_small : forall A ma mt aib slots i, WF A ->
  a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
  0 <= i < mt_cnt mt -> 0 <= i * mt_stride mt < 2^22.
Proof.
  intros A ma mt aib slots i HW Hma Hr Hi.
  destruct (wf_grp A HW ma mt aib slots Hma Hr) as
    (Hw32 & Hfr & Hsc & Hlen & Hav & _).
  pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS16.
  pose proof (w_last_range (mt_w32 mt)) as Hl. unfold mt_cnt, mt_last in Hi.
  unfold mt_stride in *.
  destruct ((mt_maplen mt =? 0) || negb (mt_last mt =? 0)) eqn:E.
  - assert (Hsc48 : mt_sc mt < 48).
    { destruct Hsc as [?|(? & Hl0 & Hm)]; [llia|]. exfalso. unfold mt_last in Hl0.
      apply Bool.orb_true_iff in E. destruct E as [E|E]; [apply Z.eqb_eq in E; llia | apply Bool.negb_true_iff in E; apply Z.eqb_neq in E; unfold mt_last in E; llia]. }
    pose proof (w_sc_range (mt_w32 mt)) as Hr2.
    pose proof (size_class_bound (mt_sc mt) ltac:(unfold mt_sc in *; llia)) as Hb.
    clear - Hi Hl Hb. lnia.
  - apply Bool.orb_false_iff in E. destruct E as [_ E]. apply Bool.negb_false_iff in E. apply Z.eqb_eq in E.
    unfold mt_last in E. assert (i = 0) by llia. subst i. llia.
Qed.

(* [comment removed for export] *)
Lemma grp_heap : forall A ma mt aib slots, WF A ->
  a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
  0x1000 <= gext_lo mt /\ gext_hi mt + 4 <= alloc_ceiling /\ (gext_hi mt + 4 <= IMG_LO \/ IMG_HI <= gext_lo mt).
Proof.
  intros A ma mt aib slots HW Hma Hr.
  destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi & _).
  destruct (wf_grp A HW mr mtr aibr slr Hmr Hrr) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpg).
  destruct (Hpg Hml) as [_ (H1 & H2 & H3 & H4)]. llia.
Qed.

Section Steps2.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.

  (* [comment removed for export] *)
  Lemma ts_lbu_mbyte : forall s a v (k : word -> M R) P,
    WIN s -> mbyte (ms_mem s) a = Some v -> 0 <= a < alloc_ceiling ->
    tsafe (k (Z_to_bv 64 v) s) P ->
    tsafe ((x <- m_lbu (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s a v k P HWn Hm Ha Hk.
    destruct (mbyte_some_rdn1 _ _ _ Hm) as (b & Hrd & Hb).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWn | llia | llia | llia] | exact Hrd |].
    rewrite Hb. exact Hk.
  Qed.
End Steps2.

End WithLayout.
