(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); ported to LPS 727298f3 (the launch input ProcInput; the CONFIG_RSEQ flag; the new auxv layout; the THP flag). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec SeqExec Hoare StoreOk MemSplit MmapSim AllocSim ShapeAlg AgentLib StepTac RefLayout VmLedger.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocCallocFacts.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Local Abbreviation u := bv_unsigned.

(* the auxv's types in [StackLayout.auxv_entries]' order: 26 pairs every launch
   carries, then AT_RSEQ_FEATURE_SIZE/AT_RSEQ_ALIGN under CONFIG_RSEQ, then AT_NULL *)
Definition AUX_KEYS (rs : bool) : list Z :=
  [33; 40; 41; 42; 43; 44; 45; 46; 47; 51; 16; 6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31]
  ++ (if rs then [27; 28] else []) ++ [0].

Lemma length_AUX_KEYS : forall rs, length (AUX_KEYS rs) = auxv_count rs.
Proof. intros [|]; reflexivity. Qed.

Lemma AUX_KEYS_range : forall rs j, 0 <= nth j (AUX_KEYS rs) 0 < 64.
Proof. intros rs j. destruct rs; do 30 (destruct j as [|j]; [cbn; lia|]); cbn; lia. Qed.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML}.

(* [comment removed for export] *)
Definition aux_addr (sp0 : word) (a : word) : Prop :=
  (u A_LIBC + 8 <= u a < u A_LIBC + 16) \/ u sp0 <= u a.

(* [comment removed for export] *)
Definition aux_env (sp0 : word) (argv envp : list (list byte)) (m : word -> option byte) : Prop :=
  exists (auxv : Z) (rs : bool) (val : nat -> word) (rnd : list byte),
    length rnd = 8%nat /\
    rdn ml_segs m (Z_to_bv 64 (u A_LIBC + 8)) 8 = Some (word_le8 (Z_to_bv 64 auxv)) /\
    u sp0 <= auxv /\ auxv + 16 * Z.of_nat (length (AUX_KEYS rs)) < 2^64 /\
    (forall j, (j < length (AUX_KEYS rs))%nat ->
       rdn ml_segs m (Z_to_bv 64 (auxv + 16 * Z.of_nat j)) 8 = Some (word_le8 (Z_to_bv 64 (nth j (AUX_KEYS rs) 0))) /\
       rdn ml_segs m (Z_to_bv 64 (auxv + 16 * Z.of_nat j + 8)) 8 = Some (word_le8 (val j))) /\
    u sp0 <= u (val 24%nat) + 8 /\ u (val 24%nat) + 24 < 2^64 /\
    rdn ml_segs m (Z_to_bv 64 (u (val 24%nat) + 8)) 8 = Some rnd.

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
  intros sp0 argv envp m m' (auxv & rs & val & rnd & Hlr & Hcell & Hlo & Hhi & Hent & Hrp1 & Hrp2 & Hrnd) Hf.
  pose proof (u64_range A_LIBC) as R1. pose proof (u64_range sp0) as R2. pose proof (mlo_order_libc (ML:=ML)) as O1.
  pose proof (mlo_order_ctx (ML:=ML)) as O2. pose proof (mlo_order_replaced (ML:=ML)) as O3. pose proof (mlo_ctx (ML:=ML)) as O4.
  pose proof (mlo_hull (ML:=ML)) as O5.
  exists auxv, rs, val, rnd. split; [exact Hlr|]. split.
  { apply (rdn_frame8 m); [lia | unfold CTX_SIZE in *; lia | | exact Hcell]. intros x Hx. apply Hf. left. lia. }
  split; [exact Hlo|]. split; [exact Hhi|]. split.
  { intros j Hj. destruct (Hent j Hj) as [E1 E2]. split.
    - apply (rdn_frame8 m); [lia | lia | | exact E1]. intros x Hx. apply Hf. right. lia.
    - apply (rdn_frame8 m); [lia | lia | | exact E2]. intros x Hx. apply Hf. right. lia. }
  split; [exact Hrp1|]. split; [exact Hrp2|].
  apply (rdn_frame8 m); [pose proof (u64_range (val 24%nat)); lia | lia | | exact Hrnd].
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
    induction t as [a st'| |req vm kf IH1 ko IH2|kd thp len vm kf IH1 ko IH2|addr len k1 IH1 k2 IH2 k3 IH3|addr len vm kf IH1 ko IH2];
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
    intros argv envp (auxv & rs & val & rnd & Hlr & Hcell & Hlo & Hhi & Hent & Hrp1 & Hrp2 & Hrnd).
    pose proof (u64_range sp0) as Hsp.
    (* [AUX_KEYS rs] is 27 or 29 long.  Both bounds are needed: the upper one
       keeps [Hhi] usable, and the lower one is what lets [lia] bound [auxv]
       at the AT_RANDOM entry (j = 24), where no [j < length (AUX_KEYS rs)]
       hypothesis is in scope.  With [rs] a variable, [length (AUX_KEYS rs)]
       is an opaque atom, so neither bound is computed by [lia] itself. *)
    assert (HL : (length (AUX_KEYS rs) <= 29)%nat) by (destruct rs; cbn; lia).
    assert (HLlo : (27 <= length (AUX_KEYS rs))%nat) by (destruct rs; cbn; lia).
    exists auxv, (le_val rnd). split; [exact Hcell|]. split; [lia|].
    intros k P sec0 Hk.
    set (rp := u (val 24%nat)) in *.
    (* a key that is neither AT_RANDOM nor AT_NULL: the loop moves on *)
    assert (STEP : forall fuel (j : nat) sec,
      (j < length (AUX_KEYS rs))%nat ->
      nth j (AUX_KEYS rs) 0 <> 25 -> nth j (AUX_KEYS rs) 0 <> 0 ->
      tsafe ((x <- m_scan_auxv fuel (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat (S j))) sec ;; k x) s) P ->
      tsafe ((x <- m_scan_auxv (S fuel) (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat j)) sec ;; k x) s) P).
    { intros fuel j sec Hj Hn25 Hn0 HH. rewrite scan_unfold. apply ts_assoc3.
      destruct (Hent j Hj) as [Hkey _].
      pose proof (AUX_KEYS_range rs j) as Hr.
      replace (v_add (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat j))) with (Z_to_bv 64 (auxv + 16 * Z.of_nat j))
        by (unfold v_add; rewrite !u64_lit by lia; reflexivity).
      eapply ts_ld_above; [lia | lia | exact Hkey |]. rewrite le_val_le8.
      assert (Hk25 : c_eq (Z_to_bv 64 (nth j (AUX_KEYS rs) 0)) (wlit 25) = false).
      { unfold wlit. apply c_eq_neq. rewrite !u64_lit by lia. exact Hn25. }
      assert (Hk0 : is0 (Z_to_bv 64 (nth j (AUX_KEYS rs) 0)) = false).
      { apply is0_false. rewrite u64_lit by lia. exact Hn0. }
      rewrite Hk25, Hk0.
      replace (v_addi (Z_to_bv 64 (16 * Z.of_nat j)) 16) with (Z_to_bv 64 (16 * Z.of_nat (S j)))
        by (unfold v_addi; rewrite u64_lit by lia; f_equal; lia).
      exact HH. }
    (* AT_NULL at [j]: the loop returns the secret it holds *)
    assert (NULL : forall fuel (j : nat) sec,
      (j < length (AUX_KEYS rs))%nat -> nth j (AUX_KEYS rs) 0 = 0 ->
      tsafe (k sec s) P ->
      tsafe ((x <- m_scan_auxv (S fuel) (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat j)) sec ;; k x) s) P).
    { intros fuel j sec Hj H0 HH. rewrite scan_unfold. apply ts_assoc3.
      destruct (Hent j Hj) as [Hkey _].
      replace (v_add (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat j))) with (Z_to_bv 64 (auxv + 16 * Z.of_nat j))
        by (unfold v_add; rewrite !u64_lit by lia; reflexivity).
      eapply ts_ld_above; [lia | lia | exact Hkey |]. rewrite le_val_le8. rewrite H0.
      replace (c_eq (Z_to_bv 64 0) (wlit 25)) with false by (symmetry; apply c_eq_neq; reflexivity || (cbn; discriminate)).
      replace (is0 (Z_to_bv 64 0)) with true by (symmetry; apply is0_true; reflexivity).
      exact HH. }
    unfold AUXV_FUEL. unfold w0. change (Z_to_bv 64 0) with (Z_to_bv 64 (16 * Z.of_nat 0)) at 1.
    do 24 (apply STEP; [destruct rs; cbn; lia | cbn; lia | cbn; lia |]).
    (* [comment removed for export] *)
    rewrite scan_unfold. apply ts_assoc3.
    destruct (Hent 24%nat ltac:(destruct rs; cbn; lia)) as [Hkey Hval].
    replace (v_add (Z_to_bv 64 auxv) (Z_to_bv 64 (16 * Z.of_nat 24))) with (Z_to_bv 64 (auxv + 16 * Z.of_nat 24))
      by (unfold v_add; rewrite !u64_lit by lia; reflexivity).
    eapply ts_ld_above; [lia | lia | exact Hkey |]. rewrite le_val_le8.
    replace (c_eq (Z_to_bv 64 (nth 24 (AUX_KEYS rs) 0)) (wlit 25)) with true by (symmetry; apply c_eq_refl).
    apply ts_assoc3.
    replace (at_ (Z_to_bv 64 (auxv + 16 * Z.of_nat 24)) 8) with (Z_to_bv 64 (auxv + 16 * Z.of_nat 24 + 8))
      by (unfold at_; rewrite u64_lit by lia; reflexivity).
    eapply ts_ld_above; [lia | lia | exact Hval |]. rewrite le_val_le8.
    apply ts_assoc3. unfold massert.
    replace (c_ltu (val 24%nat) (wlit (2^64 - 24))) with true
      by (symmetry; unfold c_ltu, bv_ltu, wlit; rewrite u64_lit by lia; apply Z.ltb_lt; lia).
    unfold mbind at 1. cbn [mret tbind].
    apply ts_assoc3.
    replace (at_ (val 24%nat) 8) with (Z_to_bv 64 (rp + 8))
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
    replace (v_addi (Z_to_bv 64 (16 * Z.of_nat 24)) 16) with (Z_to_bv 64 (16 * Z.of_nat 25))
      by (unfold v_addi; rewrite u64_lit by lia; f_equal; lia).
    (* AT_EXECFN, then (CONFIG_RSEQ) AT_RSEQ_FEATURE_SIZE and AT_RSEQ_ALIGN, then AT_NULL *)
    apply STEP; [destruct rs; cbn; lia | cbn; lia | cbn; lia |].
    destruct rs.
    - apply STEP; [cbn; lia | cbn; lia | cbn; lia |].
      apply STEP; [cbn; lia | cbn; lia | cbn; lia |].
      apply NULL; [cbn; lia | reflexivity | exact Hk].
    - apply NULL; [cbn; lia | reflexivity | exact Hk].
  Qed.
End Scan.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aux_env_intro : forall inp mbase ph entry (sp0 brk : word) draw (m : word -> option byte),
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase draw) inp ->
  sp_window_lo <= u sp0 -> u sp0 <= sp_window_hi -> u sp0 mod 16 = 0 ->
  (forall a : word, u sp0 <= u a -> m a = stack_to_mem sp0 (entry_stack_image inp mbase ph entry sp0 draw) a) ->
  rdn ml_segs m (Z_to_bv 64 (u A_LIBC + 8)) 8
  = Some (word_le8 (Z_to_bv 64 (u sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp))))) ->
  aux_env sp0 (in_argv inp) (in_envp inp) m.
Proof.
  intros inp mbase ph entry sp0 brk draw m Hva Hve Hvl Hlau Hlo Hhi Hal Hstk Hcell.
  pose proof (u64_range sp0) as Hsp.
  set (rs := kb_rseq (in_kernel inp)).
  set (stk := stack_to_mem sp0 (entry_stack_image inp mbase ph entry sp0 draw)) in *.
  set (AW := auxv_words (launch_auxv inp sp0 mbase) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp)
               (at_random_ptr sp0 rs (in_argv inp) (in_envp inp))
               (at_execfn_ptr (ed_top draw) (in_execfn inp))).
  assert (RAW : forall j, (j < 2 * auxv_count rs)%nat ->
            rdn ml_segs stk (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j)) 8%nat
            = Some (word_le8 (nth j AW (Z_to_bv 64 0)))).
  { intros j Hj. unfold stk, AW, rs. eapply read_auxv_word;
      first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hlo | exact Hhi | exact Hj ]. }
  assert (RF :
    (u sp0 <= u (at_random_ptr sp0 rs (in_argv inp) (in_envp inp)))
    /\ (u (at_random_ptr sp0 rs (in_argv inp) (in_envp inp)) + 16
        <= u sp0 + Z.of_nat (length (entry_stack_image inp mbase ph entry sp0 draw)))
    /\ (u sp0 + Z.of_nat (length (entry_stack_image inp mbase ph entry sp0 draw)) < 2^64)
    /\ (u (at_random_ptr sp0 rs (in_argv inp) (in_envp inp)) mod 8 = 0)
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn ml_segs stk
            (Z_to_bv 64 (u (at_random_ptr sp0 rs (in_argv inp) (in_envp inp)) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random draw)))))).
  { unfold stk, rs. eapply rnd_facts;
      first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hlo | exact Hhi | exact Hal ]. }
  destruct RF as (R1 & R2 & R3 & R4 & R5).
  assert (KEYS : forall j, (j < length (AUX_KEYS rs))%nat ->
            nth (2 * j) AW (Z_to_bv 64 0) = Z_to_bv 64 (nth j (AUX_KEYS rs) 0)).
  { unfold AW, auxv_words, auxv_entries, rs.
    change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)).
    destruct (kb_rseq (in_kernel inp)); intros j Hj;
      do 29 (destruct j as [|j]; [reflexivity|]); cbn in Hj; lia. }
  assert (HL : length (AUX_KEYS rs) = auxv_count rs) by apply length_AUX_KEYS.
  assert (HC : (auxv_count rs <= 29)%nat) by (unfold auxv_count; destruct rs; lia).
  assert (RD : forall (a : Z) n bs, u sp0 <= a -> a + Z.of_nat n < 2^64 ->
            rdn ml_segs stk (Z_to_bv 64 a) n = Some bs -> rdn ml_segs m (Z_to_bv 64 a) n = Some bs).
  { intros a n bs Ha Hn Hr. rewrite <- Hr. apply rdn_ext; rewrite u64_lit by lia; [lia|].
    intros x Hx. apply Hstk. lia. }
  pose proof (bsb_bound Sv48 inp mbase ph entry sp0 brk draw Hvl Hlau) as Hbl.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hla. pose proof Hve as [Hle _].
  assert (Hoff : (Z.of_nat (auxv_off (in_argv inp) (in_envp inp)) <= 8 + 8 * 1025 + 8 * 257)%Z)
    by (unfold auxv_off; lia).
  assert (Hrp : nth (2 * 24 + 1) AW (Z_to_bv 64 0) = at_random_ptr sp0 rs (in_argv inp) (in_envp inp))
    by (unfold AW, auxv_words, auxv_entries; reflexivity).
  exists (u sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp))), rs,
         (fun j => nth (2 * j + 1) AW (Z_to_bv 64 0)),
         (firstn 8 (skipn 8 (at_random_bytes (ed_random draw)))).
  split; [reflexivity|]. split; [exact Hcell|].
  split; [lia|]. split; [unfold sp_window_hi in Hhi; rewrite HL; lia|]. split.
  { intros j Hj. rewrite HL in Hj. split.
    - apply RD; [lia | unfold sp_window_hi in Hhi; lia|].
      rewrite <- (KEYS j ltac:(rewrite HL; exact Hj)).
      replace (Z_to_bv 64 (u sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp)) + 16 * Z.of_nat j))
        with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * (2 * j)))%bv
        by (rewrite word_add_nat; f_equal; lia).
      apply RAW. lia.
    - apply RD; [lia | unfold sp_window_hi in Hhi; lia|].
      replace (Z_to_bv 64 (u sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp)) + 16 * Z.of_nat j + 8))
        with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * (2 * j + 1)))%bv
        by (rewrite word_add_nat; f_equal; lia).
      apply RAW. lia. }
  cbv beta. rewrite Hrp.
  unfold sp_window_hi in Hhi.
  split; [lia|]. split; [lia|].
  apply RD; [lia | cbn; lia|].
  apply (R5 8%nat 8%nat). lia.
Qed.

End WithLayout.
