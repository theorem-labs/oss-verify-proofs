(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec SeqExec Hoare StoreOk MemSplit MmapSim AllocSim ShapeAlg AgentLib StepTac RefLayout VmLedger.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocCallocFacts.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Local Abbreviation u := bv_unsigned.

(* [comment removed for export] *)
Definition AUX_KEYS : list Z := [3; 4; 5; 16; 6; 11; 12; 23; 25; 0].

Lemma AUX_KEYS_spec : forall ph rnd uid hw j, (j < 10)%nat ->
  nth (2 * j) (auxv_words ph rnd uid hw) (Z_to_bv 64 0) = Z_to_bv 64 (nth j AUX_KEYS 0).
Proof.
  intros ph rnd uid hw j Hj.
  do 10 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML}.

(* [comment removed for export] *)
Definition aux_addr (sp0 : word) (a : word) : Prop :=
  (u A_LIBC + 8 <= u a < u A_LIBC + 16) \/ u sp0 <= u a.

(* [comment removed for export] *)
Definition aux_env (sp0 : word) (argv envp : list (list byte)) (m : word -> option byte) : Prop :=
  exists (auxv : Z) (vals : list word) (rnd : list byte),
    length vals = 10%nat /\ length rnd = 8%nat /\
    rdn ml_segs m (Z_to_bv 64 (u A_LIBC + 8)) 8 = Some (word_le8 (Z_to_bv 64 auxv)) /\
    u sp0 <= auxv /\ auxv + 160 < 2^64 /\
    (forall j, (j < 10)%nat ->
       rdn ml_segs m (Z_to_bv 64 (auxv + 16 * Z.of_nat j)) 8 = Some (word_le8 (Z_to_bv 64 (nth j AUX_KEYS 0))) /\
       rdn ml_segs m (Z_to_bv 64 (auxv + 16 * Z.of_nat j + 8)) 8 = Some (word_le8 (nth j vals (Z_to_bv 64 0)))) /\
    u sp0 <= u (nth 8%nat vals (Z_to_bv 64 0)) + 8 /\ u (nth 8%nat vals (Z_to_bv 64 0)) + 24 < 2^64 /\
    rdn ml_segs m (Z_to_bv 64 (u (nth 8%nat vals (Z_to_bv 64 0)) + 8)) 8 = Some rnd.

Lemma rdn_frame8 : forall m m' (a : Z) bs,
  0 <= a -> a + 8 <= 2^64 ->
  (forall x : word, a <= u x < a + 8 -> m' x = m x) ->
  rdn ml_segs m (Z_to_bv 64 a) 8 = Some bs -> rdn ml_segs m' (Z_to_bv 64 a) 8 = Some bs.
Proof.
  intros m m' a bs Ha Hnw Hf H. rewrite <- H. apply rdn_ext; rewrite u64_lit by lia; [cbn; lia|].
  intros x Hx. apply Hf. cbn in Hx. lia.
Qed.

Lemma aux_env_frame : forall sp0 argv envp m m',
  aux_env sp0 argv envp m -> (forall a : word, aux_addr sp0 a -> m' a = m a) -> aux_env sp0 argv envp m'.
Proof.
  intros sp0 argv envp m m' (auxv & vals & rnd & Hlv & Hlr & Hcell & Hlo & Hhi & Hent & Hrp1 & Hrp2 & Hrnd) Hf.
  pose proof (u64_range A_LIBC) as R1. pose proof (u64_range sp0) as R2. pose proof (mlo_order_libc (ML:=ML)) as O1.
  pose proof (mlo_order_ctx (ML:=ML)) as O2. pose proof (mlo_order_replaced (ML:=ML)) as O3. pose proof (mlo_ctx (ML:=ML)) as O4.
  pose proof (mlo_hull (ML:=ML)) as O5.
  exists auxv, vals, rnd. split; [exact Hlv|]. split; [exact Hlr|]. split.
  { apply (rdn_frame8 m); [lia | unfold CTX_SIZE in *; lia | | exact Hcell]. intros x Hx. apply Hf. left. lia. }
  split; [exact Hlo|]. split; [exact Hhi|]. split.
  { intros j Hj. destruct (Hent j Hj) as [E1 E2]. split.
    - apply (rdn_frame8 m); [lia | lia | | exact E1]. intros x Hx. apply Hf. right. lia.
    - apply (rdn_frame8 m); [lia | lia | | exact E2]. intros x Hx. apply Hf. right. lia. }
  split; [exact Hrp1|]. split; [exact Hrp2|].
  apply (rdn_frame8 m); [pose proof (u64_range (nth 8%nat vals (Z_to_bv 64 0))); lia | lia | | exact Hrnd].
  intros x Hx. apply Hf. right. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma le_val_le8 : forall w : word, le_val (word_le8 w) = w.
Proof.
  intros w. unfold le_val. rewrite bytes_le_n_to_le_8. apply Z_to_bv_bv_unsigned.
Qed.

Section Scan.
  Context {R : Type}.
  Variables (sp0 : word) (s : mstate).
  Hypothesis Hwin : IMG_HI <= ms_lo s /\ ms_lo s <= ms_hi s /\ ms_hi s <= u sp0.
  Implicit Types (P : R -> mstate -> Prop).

  (* [comment removed for export] *)
  Lemma ts_ld_acc : forall (a : word) bs (k : word -> M R) P,
    acc_ok s a (Z.of_nat 8) = true ->
    rdn ml_segs (ms_mem s) a 8 = Some bs ->
    tsafe (k (le_val bs) s) P ->
    tsafe ((x <- m_ld a ;; k x) s) P.
  Proof.
    intros a bs k P Hacc Hrd Hk. unfold mbind, m_ld, mbind, m_rd, mret. rewrite Hacc, Hrd. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_ld_above : forall (a : Z) bs (k : word -> M R) P,
    u sp0 <= a -> a + 8 <= 2^64 ->
    rdn ml_segs (ms_mem s) (Z_to_bv 64 a) 8 = Some bs ->
    tsafe (k (le_val bs) s) P ->
    tsafe ((x <- m_ld (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros a bs k P Ha Hnw Hrd Hk. unfold mbind, m_ld, mbind, m_rd, mret.
    pose proof (u64_range sp0). destruct Hwin as (W1 & W2 & W3).
    assert (Hacc : acc_ok s (Z_to_bv 64 a) (Z.of_nat 8) = true).
    { unfold acc_ok. rewrite u64_lit by lia. rewrite orb_true_iff. right. rewrite andb_true_iff, !Z.leb_le. cbn. lia. }
    rewrite Hacc, Hrd. exact Hk.
  Qed.

  Lemma scan_unfold : forall fuel auxv i secret,
    m_scan_auxv (S fuel) auxv i secret =
    (key <- m_ld (v_add auxv i) ;;
     if c_eq key (wlit 25)
     then val <- m_ld (at_ (v_add auxv i) 8) ;;
          massert (c_ltu val (wlit (2^64 - 24))) ;;
          rnd <- m_ld (at_ val 8) ;;
          auxv' <- m_ld (at_ A_LIBC 8) ;;
          m_scan_auxv fuel auxv' (v_addi i 16) rnd
     else if is0 key then mret secret
     else m_scan_auxv fuel auxv (v_addi i 16) secret).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ts_assoc3 : forall {A B} (m : M A) (f : A -> M B) (g : B -> M R) st P,
    tsafe ((x <- m ;; y <- f x ;; g y) st) P -> tsafe ((y <- (x <- m ;; f x) ;; g y) st) P.
  Proof.
    intros A B m f g st P HH. unfold mbind in *.
    revert HH. generalize (m st). intros t.
    induction t as [a st'| |req vm kf IH1 ko IH2|kd len vm kf IH1 ko IH2|addr len k1 IH1 k2 IH2 k3 IH3|addr len vm kf IH1 ko IH2];
      cbn; intros HH; try exact HH.
    - destruct HH as [X1 X2]; split; [intros Hb; apply IH1; exact (X1 Hb) | intros Hb; apply IH2; exact (X2 Hb)].
    - (* [comment removed for export] *)
      destruct HH as [X1 X2]; split; [intros Hr; apply IH1; exact (X1 Hr) | intros a Ha; apply IH2; exact (X2 a Ha)].
    - (* [comment removed for export] *) apply IH2; exact HH.
    - destruct HH as [X1 X2]; split; [intros Hb; apply IH1; exact (X1 Hb) | intros Hb; apply IH2; exact (X2 Hb)].
  Qed.

  (* [comment removed for export] *)
  Theorem scan_auxv_ok : forall argv envp,
    aux_env sp0 argv envp (ms_mem s) ->
    exists (auxv : Z) (sec : word),
      rdn ml_segs (ms_mem s) (Z_to_bv 64 (u A_LIBC + 8)) 8 = Some (word_le8 (Z_to_bv 64 auxv)) /\
      0 <= auxv < 2^64 /\
      forall (k : word -> M R) P (sec0 : word),
        tsafe (k sec s) P ->
        tsafe ((x <- m_scan_auxv AUXV_FUEL (Z_to_bv 64 auxv) w0 sec0 ;; k x) s) P.
  Proof.
    intros argv envp (auxv & vals & rnd & Hlv & Hlr & Hcell & Hlo & Hhi & Hent & Hrp1 & Hrp2 & Hrnd).
    pose proof (u64_range sp0) as Hsp.
    exists auxv, (le_val rnd). split; [exact Hcell|]. split; [lia|].
    intros k P sec0 Hk.
    set (rp := u (nth 8%nat vals (Z_to_bv 64 0))) in *.
    (* [comment removed for export] *)
    assert (STEP : forall fuel (j : nat) sec,
      (j < 8)%nat ->
      tsafe ((x <- m_scan_auxv fuel (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat (S j))) sec ;; k x) s) P ->
      tsafe ((x <- m_scan_auxv (S fuel) (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat j)) sec ;; k x) s) P).
    { intros fuel j sec Hj HH. rewrite scan_unfold. apply ts_assoc3.
      destruct (Hent j ltac:(lia)) as [Hkey _].
      replace (v_add (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat j))) with (Z_to_bv 64 (auxv + 16 * Z.of_nat j))
        by (unfold v_add; rewrite !u64_lit by lia; reflexivity).
      eapply ts_ld_above; [lia | lia | exact Hkey |]. rewrite le_val_le8.
      assert (Hk25 : c_eq (Z_to_bv 64 (nth j AUX_KEYS 0)) (wlit 25) = false).
      { unfold wlit. apply c_eq_neq. rewrite !u64_lit by (do 8 (destruct j as [|j]; [cbn; lia|]); lia).
        do 8 (destruct j as [|j]; [cbn; lia|]). lia. }
      assert (Hk0 : is0 (Z_to_bv 64 (nth j AUX_KEYS 0)) = false).
      { apply is0_false. rewrite u64_lit by (do 8 (destruct j as [|j]; [cbn; lia|]); lia).
        do 8 (destruct j as [|j]; [cbn; lia|]). lia. }
      rewrite Hk25, Hk0.
      replace (v_addi (Z_to_bv 64 (16 * Z.of_nat j)) 16) with (Z_to_bv 64 (16 * Z.of_nat (S j)))
        by (unfold v_addi; rewrite u64_lit by lia; f_equal; lia).
      exact HH. }
    unfold AUXV_FUEL. unfold w0. change (Z_to_bv 64 0) with (Z_to_bv 64 (16 * Z.of_nat 0)) at 1.
    do 8 (apply STEP; [lia|]).
    (* [comment removed for export] *)
    rewrite scan_unfold. apply ts_assoc3.
    destruct (Hent 8%nat ltac:(lia)) as [Hkey Hval].
    replace (v_add (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat 8))) with (Z_to_bv 64 (auxv + 16 * Z.of_nat 8))
      by (unfold v_add; rewrite !u64_lit by lia; reflexivity).
    eapply ts_ld_above; [lia | lia | exact Hkey |]. rewrite le_val_le8.
    replace (c_eq (Z_to_bv 64 (nth 8 AUX_KEYS 0)) (wlit 25)) with true by (symmetry; apply c_eq_refl).
    apply ts_assoc3.
    replace (at_ (Z_to_bv 64 (auxv + 16 * Z.of_nat 8)) 8) with (Z_to_bv 64 (auxv + 16 * Z.of_nat 8 + 8))
      by (unfold at_; rewrite u64_lit by lia; reflexivity).
    eapply ts_ld_above; [lia | lia | exact Hval |]. rewrite le_val_le8.
    apply ts_assoc3. unfold massert.
    replace (c_ltu (nth 8 vals (Z_to_bv 64 0)) (wlit (2^64 - 24))) with true
      by (symmetry; unfold c_ltu, bv_ltu, wlit; rewrite u64_lit by lia; apply Z.ltb_lt; lia).
    unfold mbind at 1. cbn [mret tbind].
    apply ts_assoc3.
    replace (at_ (nth 8 vals (Z_to_bv 64 0)) 8) with (Z_to_bv 64 (rp + 8))
      by (unfold at_; subst rp; reflexivity).
    eapply ts_ld_above; [lia | lia | exact Hrnd |].
    apply ts_assoc3.
    pose proof (u64_range A_LIBC). pose proof (mlo_order_libc (ML:=ML)). pose proof (mlo_order_ctx (ML:=ML)).
    pose proof (mlo_order_replaced (ML:=ML)). pose proof (mlo_ctx (ML:=ML)). pose proof (mlo_hull (ML:=ML)).
    replace (at_ A_LIBC 8) with (Z_to_bv 64 (u A_LIBC + 8)) by (unfold at_; reflexivity).
    (* [comment removed for export] *)
    assert (Hacc : acc_ok s (Z_to_bv 64 (u A_LIBC + 8)) (Z.of_nat 8) = true).
    { destruct Hwin as (W1 & W2 & W3). unfold acc_ok. rewrite u64_lit by (unfold CTX_SIZE in *; lia).
      rewrite orb_true_iff. left. apply Z.leb_le. unfold CTX_SIZE in *. cbn. lia. }
    eapply ts_ld_acc; [exact Hacc | exact Hcell |]. rewrite le_val_le8.
    replace (v_addi (Z_to_bv 64 (16 * Z.of_nat 8)) 16) with (Z_to_bv 64 (16 * Z.of_nat 9))
      by (unfold v_addi; rewrite u64_lit by lia; f_equal; lia).
    (* [comment removed for export] *)
    rewrite scan_unfold. apply ts_assoc3.
    destruct (Hent 9%nat ltac:(lia)) as [Hkey9 _].
    replace (v_add (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat 9))) with (Z_to_bv 64 (auxv + 16 * Z.of_nat 9))
      by (unfold v_add; rewrite !u64_lit by lia; reflexivity).
    eapply ts_ld_above; [lia | lia | exact Hkey9 |]. rewrite le_val_le8.
    replace (c_eq (Z_to_bv 64 (nth 9 AUX_KEYS 0)) (wlit 25)) with false by (symmetry; apply c_eq_neq; reflexivity || (cbn; discriminate)).
    replace (is0 (Z_to_bv 64 (nth 9 AUX_KEYS 0))) with true by (symmetry; apply is0_true; reflexivity).
    exact Hk.
  Qed.
End Scan.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aux_vals (ph : PhdrInfo) (rnd uid hw : word) : list word :=
  [Z_to_bv 64 (Z.of_N (ph_addr ph)); Z_to_bv 64 (Z.of_N (ph_ent ph)); Z_to_bv 64 (Z.of_N (ph_num ph)); hw;
   Z_to_bv 64 4096; uid; uid; Z_to_bv 64 0; rnd; Z_to_bv 64 0].

Lemma aux_vals_spec : forall ph rnd uid hw j, (j < 10)%nat ->
  nth (2 * j + 1) (auxv_words ph rnd uid hw) (Z_to_bv 64 0) = nth j (aux_vals ph rnd uid hw) (Z_to_bv 64 0).
Proof.
  intros ph rnd uid hw j Hj.
  do 10 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma aux_env_intro : forall ph (sp0 : word) argv envp uid hw draw (m : word -> option byte),
  valid_argv argv -> valid_envp envp ->
  sp_window_lo <= u sp0 -> u sp0 <= sp_window_hi -> u sp0 mod 16 = 0 ->
  (forall a : word, u sp0 <= u a -> m a = stack_to_mem sp0 (entry_stack_image ph sp0 argv envp uid hw draw) a) ->
  rdn ml_segs m (Z_to_bv 64 (u A_LIBC + 8)) 8 = Some (word_le8 (Z_to_bv 64 (u sp0 + Z.of_nat (auxv_off argv envp)))) ->
  aux_env sp0 argv envp m.
Proof.
  intros ph sp0 argv envp uid hw draw m Hva Hve Hlo Hhi Hal Hstk Hcell.
  pose proof (u64_range sp0) as Hsp.
  set (stk := stack_to_mem sp0 (entry_stack_image ph sp0 argv envp uid hw draw)) in *.
  set (bsb := build_stack_bytes ph sp0 argv envp uid hw draw).
  pose proof (lay_bsb_nw ph sp0 draw argv envp uid hw Hva Hve Hhi) as Hnw. fold bsb in Hnw.
  pose proof (lay_bsb_len ph sp0 draw argv envp uid hw Hva Hve) as Hlen. fold bsb in Hlen.
  destruct (rnd_facts ml_segs ph sp0 draw argv envp uid hw Hva Hve Hlo Hhi Hal) as (R1 & R2 & R3 & R4 & R5). fold bsb in R2, R3.
  set (rp := at_random_ptr sp0 argv envp) in *.
  pose proof (auxv_off_bound ph sp0 draw argv envp uid hw) as Hoff. fold bsb in Hoff.
  assert (RD : forall (a : Z) n bs, u sp0 <= a -> a + Z.of_nat n < 2^64 ->
            rdn ml_segs stk (Z_to_bv 64 a) n = Some bs -> rdn ml_segs m (Z_to_bv 64 a) n = Some bs).
  { intros a n bs Ha Hn Hr. rewrite <- Hr. apply rdn_ext; rewrite u64_lit by lia; [lia|].
    intros x Hx. apply Hstk. lia. }
  exists (u sp0 + Z.of_nat (auxv_off argv envp)), (aux_vals ph rp uid hw), (firstn 8 (skipn 8 (at_random_bytes (ed_random draw)))).
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hcell|].
  split; [lia|]. split; [unfold sp_window_hi in Hhi; lia|]. split.
  { intros j Hj. split.
    - apply RD; [lia | unfold sp_window_hi in Hhi; lia|].
      rewrite <- (AUX_KEYS_spec ph rp uid hw j Hj).
      replace (Z_to_bv 64 (u sp0 + Z.of_nat (auxv_off argv envp) + 16 * Z.of_nat j))
        with (sp0 + nat_to_word (auxv_off argv envp + 8 * (2 * j)))%bv
        by (rewrite word_add_nat; f_equal; lia).
      apply (read_auxv_word ml_segs ph sp0 draw argv envp uid hw Hva Hve Hhi). lia.
    - apply RD; [lia | unfold sp_window_hi in Hhi; lia|].
      rewrite <- (aux_vals_spec ph rp uid hw j Hj).
      replace (Z_to_bv 64 (u sp0 + Z.of_nat (auxv_off argv envp) + 16 * Z.of_nat j + 8))
        with (sp0 + nat_to_word (auxv_off argv envp + 8 * (2 * j + 1)))%bv
        by (rewrite word_add_nat; f_equal; lia).
      apply (read_auxv_word ml_segs ph sp0 draw argv envp uid hw Hva Hve Hhi). lia. }
  cbn [nth aux_vals].
  split; [lia|]. split; [unfold sp_window_hi in Hhi; lia|].
  apply RD; [lia | unfold sp_window_hi in Hhi; cbn; lia|].
  apply (R5 8%nat 8%nat). lia.
Qed.

End WithLayout.
